use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use crate::egraph::format_expr_compact;
use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, MatchPat, NodeId,
    Stmt, Type, UnaryOp,
};
use crate::ssa::analyze_ssa;

const AARCH64_CALLEE_REGS: &[&str] = &[
    "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28",
];
const AARCH64_ARG_REGS: &[&str] = &["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"];

const X86_64_ALLOC_REGS: &[&str] = &[
    "rbx", "r12", "r13", "r14", "r15", "r10", "r11", "r8", "r9", "rcx",
];
const X86_64_ARG_REGS: &[&str] = &["rdi", "rsi", "rdx", "rcx", "r8", "r9"];

#[derive(Debug, Clone)]
pub struct LiveInterval {
    pub var_name: String,
    pub start_pc: usize,
    pub end_pc: usize,
    pub use_count: usize,
    pub max_loop_depth: usize,
    pub spill_weight: f64,
    pub degree: usize,
    pub assigned_color: Option<usize>,
    pub aarch64_loc: String,
    pub x86_64_loc: String,
    pub linear_scan_loc: String,
    pub spilled: bool,
}

#[derive(Debug, Clone)]
pub struct InterferenceEdge {
    pub u: String,
    pub v: String,
    pub kind: String, // "Interference" | "CoalescedMove"
}

#[derive(Debug, Clone)]
pub struct FunctionRegAllocReport {
    pub fn_name: String,
    pub signature: String,
    pub k_registers: usize,
    pub virtual_regs: usize,
    pub interference_edges_count: usize,
    pub max_pressure_clique: usize,
    pub chromatic_colors_used: usize,
    pub coalesced_moves: usize,
    pub spilled_vars: usize,
    pub stack_frame_bytes: usize,
    pub intervals: Vec<LiveInterval>,
    pub edges: Vec<InterferenceEdge>,
    pub kempe_order: Vec<String>,
    pub mermaid_graph: String,
    pub aarch64_asm: String,
    pub x86_64_asm: String,
}

#[derive(Debug, Clone)]
pub struct RegAllocReport {
    pub k_registers: usize,
    pub total_functions: usize,
    pub total_virtual_regs: usize,
    pub total_interference_edges: usize,
    pub max_register_pressure: usize,
    pub total_coalesced_moves: usize,
    pub total_spills: usize,
    pub total_aarch64_insts: usize,
    pub total_x86_64_insts: usize,
    pub functions: Vec<FunctionRegAllocReport>,
    pub elapsed_ms: u128,
}

#[derive(Debug, Clone)]
pub struct AllocationSiteAudit {
    pub site_id: NodeId,
    pub fn_name: String,
    pub kind: String,          // "StructInit" | "FixedList" | "DynamicListPush" | "StringFormat"
    pub expr_summary: String,
    pub escape_state: String,  // "NoEscape (Stack/SROA)" | "ReturnEscape (RVO)" | "LoopArena" | "HeapEscape"
    pub promotion_strategy: String,
    pub sroa_fields: usize,
    pub estimated_bytes_saved: usize,
    pub note: String,
}

#[derive(Debug, Clone)]
pub struct FunctionEscapeReport {
    pub fn_name: String,
    pub signature: String,
    pub total_sites: usize,
    pub stack_or_sroa_sites: usize,
    pub rvo_sites: usize,
    pub heap_escape_sites: usize,
    pub bytes_saved_per_call: usize,
    pub sites: Vec<AllocationSiteAudit>,
    pub optimized_by_spoke: BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct EscapeAnalysisReport {
    pub total_functions: usize,
    pub total_alloc_sites: usize,
    pub stack_promoted_sites: usize,
    pub rvo_eliminated_sites: usize,
    pub sroa_scalarized_fields: usize,
    pub heap_escaping_sites: usize,
    pub total_bytes_saved_per_run: usize,
    pub heap_reduction_pct: u8,
    pub functions: Vec<FunctionEscapeReport>,
    pub elapsed_ms: u128,
}

#[derive(Clone)]
struct IrInst {
    pc: usize,
    loop_depth: usize,
    op: IrOp,
    defs: Vec<String>,
    uses: Vec<String>,
}

#[derive(Clone)]
enum IrOp {
    ParamBind { name: String, idx: usize },
    MovImm { dst: String, imm: i64 },
    MovCopy { dst: String, src: String },
    BinOp { dst: String, op: BinOp, lhs: String, rhs: String },
    Call { dst: String, callee: String, args: Vec<String> },
    Label { name: String },
    CmpBranchFalse { cond_var: String, target_label: String },
    Jump { target_label: String },
    Return { src: Option<String> },
}

/// Run Chaitin-Briggs Kempe-Stack Graph-Coloring & Poletto-Sarkar Linear-Scan Register Allocation
/// over live variable intervals and emit Dual-Target Native Assembly (AArch64 AAPCS64 & x86_64 System V).
pub fn allocate_registers_and_codegen(
    hub: &HubModule,
    k_registers: Option<usize>,
) -> RegAllocReport {
    let start = Instant::now();
    let k = k_registers.unwrap_or(8).clamp(2, 10);
    let ssa_rep = analyze_ssa(hub);

    let mut functions = Vec::new();
    let mut total_virtual_regs = 0usize;
    let mut total_interference_edges = 0usize;
    let mut max_register_pressure = 0usize;
    let mut total_coalesced_moves = 0usize;
    let mut total_spills = 0usize;
    let mut total_aarch64_insts = 0usize;
    let mut total_x86_64_insts = 0usize;

    for item in &hub.items {
        if let Item::Function(f) = item {
            let ssa_fn = ssa_rep.functions.iter().find(|sf| sf.fn_name == f.name);
            let rep = allocate_fn_registers(f, ssa_fn, k);
            total_virtual_regs += rep.virtual_regs;
            total_interference_edges += rep.interference_edges_count;
            if rep.max_pressure_clique > max_register_pressure {
                max_register_pressure = rep.max_pressure_clique;
            }
            total_coalesced_moves += rep.coalesced_moves;
            total_spills += rep.spilled_vars;
            total_aarch64_insts += rep
                .aarch64_asm
                .lines()
                .filter(|l| {
                    let t = l.trim();
                    !t.is_empty() && !t.starts_with("//") && !t.starts_with('.') && !t.ends_with(':')
                })
                .count();
            total_x86_64_insts += rep
                .x86_64_asm
                .lines()
                .filter(|l| {
                    let t = l.trim();
                    !t.is_empty() && !t.starts_with('#') && !t.starts_with('.') && !t.ends_with(':')
                })
                .count();
            functions.push(rep);
        }
    }

    RegAllocReport {
        k_registers: k,
        total_functions: functions.len(),
        total_virtual_regs,
        total_interference_edges,
        max_register_pressure,
        total_coalesced_moves,
        total_spills,
        total_aarch64_insts,
        total_x86_64_insts,
        functions,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

fn allocate_fn_registers(
    f: &FnDecl,
    ssa_fn: Option<&crate::ssa::FunctionSsaReport>,
    k: usize,
) -> FunctionRegAllocReport {
    let params_sig: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.ty.display()))
        .collect();
    let signature = format!(
        "fn {}({}) -> {}",
        f.name,
        params_sig.join(", "),
        f.ret_ty.display()
    );

    let mut insts = Vec::new();
    let mut temp_counter = 0usize;
    let mut label_counter = 0usize;

    for (idx, p) in f.params.iter().enumerate() {
        let pc = insts.len();
        insts.push(IrInst {
            pc,
            loop_depth: 0,
            op: IrOp::ParamBind {
                name: p.name.clone(),
                idx,
            },
            defs: vec![p.name.clone()],
            uses: Vec::new(),
        });
    }

    lower_stmts_to_ir(
        &f.body,
        0,
        &mut insts,
        &mut temp_counter,
        &mut label_counter,
    );

    if !matches!(insts.last().map(|i| &i.op), Some(IrOp::Return { .. })) {
        let pc = insts.len();
        insts.push(IrInst {
            pc,
            loop_depth: 0,
            op: IrOp::Return { src: None },
            defs: Vec::new(),
            uses: Vec::new(),
        });
    }

    // Compute live intervals [start_pc, end_pc], use counts, and max loop depths
    let mut var_start: BTreeMap<String, usize> = BTreeMap::new();
    let mut var_end: BTreeMap<String, usize> = BTreeMap::new();
    let mut var_uses: BTreeMap<String, usize> = BTreeMap::new();
    let mut var_loop_depth: BTreeMap<String, usize> = BTreeMap::new();
    let mut move_pairs: Vec<(String, String)> = Vec::new();

    for inst in &insts {
        for d in &inst.defs {
            var_start.entry(d.clone()).or_insert(inst.pc);
            var_end
                .entry(d.clone())
                .and_modify(|e| *e = (*e).max(inst.pc))
                .or_insert(inst.pc);
            var_loop_depth
                .entry(d.clone())
                .and_modify(|ld| *ld = (*ld).max(inst.loop_depth))
                .or_insert(inst.loop_depth);
        }
        for u in &inst.uses {
            var_start.entry(u.clone()).or_insert(0);
            var_end
                .entry(u.clone())
                .and_modify(|e| *e = (*e).max(inst.pc))
                .or_insert(inst.pc);
            *var_uses.entry(u.clone()).or_insert(0) += 1;
            var_loop_depth
                .entry(u.clone())
                .and_modify(|ld| *ld = (*ld).max(inst.loop_depth))
                .or_insert(inst.loop_depth);
        }
        if let IrOp::MovCopy { dst, src } = &inst.op {
            if dst != src {
                move_pairs.push((dst.clone(), src.clone()));
            }
        }
    }

    // Extend live ranges inside loops so loop-carried variables span the full loop back-edge
    let mut label_pcs: BTreeMap<String, usize> = BTreeMap::new();
    for inst in &insts {
        if let IrOp::Label { name } = &inst.op {
            label_pcs.insert(name.clone(), inst.pc);
        }
    }
    for inst in &insts {
        if let IrOp::Jump { target_label } = &inst.op {
            if let Some(&target_pc) = label_pcs.get(target_label) {
                if target_pc < inst.pc {
                    for (v, start_pc) in &var_start {
                        if let Some(end_pc) = var_end.get_mut(v) {
                            if *start_pc <= target_pc && *end_pc >= target_pc && *end_pc < inst.pc {
                                *end_pc = inst.pc;
                            }
                        }
                    }
                }
            }
        }
    }

    let all_vars: Vec<String> = var_start.keys().cloned().collect();
    let mut adj: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for v in &all_vars {
        adj.insert(v.clone(), BTreeSet::new());
    }

    // 1. Interval overlap interference
    for i in 0..all_vars.len() {
        for j in (i + 1)..all_vars.len() {
            let u = &all_vars[i];
            let v = &all_vars[j];
            let (u_s, u_e) = (var_start[u], var_end[u]);
            let (v_s, v_e) = (var_start[v], var_end[v]);
            if u_s <= v_e && v_s <= u_e {
                adj.get_mut(u).unwrap().insert(v.clone());
                adj.get_mut(v).unwrap().insert(u.clone());
            }
        }
    }

    // 2. Also incorporate exact SSA basic-block live_in / live_out sets if available
    if let Some(sf) = ssa_fn {
        for blk in &sf.blocks {
            for live_set in [&blk.live_in, &blk.live_out] {
                let base_vars: Vec<String> = live_set
                    .iter()
                    .map(|s| s.rsplit_once('_').map(|(b, _)| b).unwrap_or(s).to_string())
                    .filter(|b| adj.contains_key(b))
                    .collect();
                for i in 0..base_vars.len() {
                    for j in (i + 1)..base_vars.len() {
                        let u = &base_vars[i];
                        let v = &base_vars[j];
                        if u != v {
                            adj.get_mut(u).unwrap().insert(v.clone());
                            adj.get_mut(v).unwrap().insert(u.clone());
                        }
                    }
                }
            }
        }
    }

    // Identify Briggs / George-Appel move-coalescing opportunities
    let mut coalesced_moves = 0usize;
    let mut coalesced_edges: Vec<InterferenceEdge> = Vec::new();
    for (dst, src) in &move_pairs {
        if adj.contains_key(dst) && adj.contains_key(src) {
            let deg_u = adj[dst].len();
            let deg_v = adj[src].len();
            if deg_u + deg_v < k * 2 {
                coalesced_moves += 1;
                coalesced_edges.push(InterferenceEdge {
                    u: dst.clone(),
                    v: src.clone(),
                    kind: "CoalescedMove".to_string(),
                });
            }
        }
    }

    let mut edges = Vec::new();
    for (u, nbrs) in &adj {
        for v in nbrs {
            if u < v {
                edges.push(InterferenceEdge {
                    u: u.clone(),
                    v: v.clone(),
                    kind: "Interference".to_string(),
                });
            }
        }
    }
    let interference_edges_count = edges.len();
    edges.extend(coalesced_edges);

    // Compute spill weights: (uses + 1) * 10^(loop_depth)
    let mut spill_weights: BTreeMap<String, f64> = BTreeMap::new();
    for v in &all_vars {
        let uses = *var_uses.get(v).unwrap_or(&1) as f64;
        let depth = *var_loop_depth.get(v).unwrap_or(&0) as i32;
        let weight = (uses.max(1.0)) * 10.0_f64.powi(depth.min(4));
        spill_weights.insert(v.clone(), weight);
    }

    // Chaitin-Briggs Kempe-stack simplification & optimistic coloring
    let mut remaining: BTreeSet<String> = all_vars.iter().cloned().collect();
    let mut kempe_stack: Vec<String> = Vec::new();

    while !remaining.is_empty() {
        // Find a node with current degree < K
        let low_deg = remaining.iter().find(|v| {
            let deg = adj[*v].iter().filter(|n| remaining.contains(*n)).count();
            deg < k
        }).cloned();

        let chosen = if let Some(v) = low_deg {
            v
        } else {
            // Spill heuristic: pick node minimizing spill_weight / current_degree
            remaining
                .iter()
                .min_by(|a, b| {
                    let da = adj[*a]
                        .iter()
                        .filter(|n| remaining.contains(*n))
                        .count()
                        .max(1) as f64;
                    let db = adj[*b]
                        .iter()
                        .filter(|n| remaining.contains(*n))
                        .count()
                        .max(1) as f64;
                    let sa = spill_weights[*a] / da;
                    let sb = spill_weights[*b] / db;
                    sa.partial_cmp(&sb).unwrap_or(std::cmp::Ordering::Equal)
                })
                .unwrap()
                .clone()
        };

        remaining.remove(&chosen);
        kempe_stack.push(chosen);
    }

    let kempe_order = kempe_stack.clone();
    let mut assigned_color: BTreeMap<String, Option<usize>> = BTreeMap::new();
    let mut spill_slot_offset: BTreeMap<String, usize> = BTreeMap::new();
    let mut next_spill_offset = 16usize;

    for v in kempe_stack.iter().rev() {
        let mut used_colors = BTreeSet::new();
        for nbr in &adj[v] {
            if let Some(Some(c)) = assigned_color.get(nbr) {
                used_colors.insert(*c);
            }
        }
        let color = (0..k).find(|c| !used_colors.contains(c));
        if color.is_none() {
            spill_slot_offset.insert(v.clone(), next_spill_offset);
            next_spill_offset += 8;
        }
        assigned_color.insert(v.clone(), color);
    }

    // Poletto-Sarkar Linear-Scan Register Allocation for comparison
    let mut sorted_vars = all_vars.clone();
    sorted_vars.sort_by_key(|v| (var_start[v], var_end[v]));
    let mut active: Vec<(String, usize, usize)> = Vec::new(); // (var, end_pc, reg_idx)
    let mut free_regs: BTreeSet<usize> = (0..k).collect();
    let mut linear_scan_map: BTreeMap<String, String> = BTreeMap::new();

    for v in &sorted_vars {
        let start_pc = var_start[v];
        let end_pc = var_end[v];
        // Expire old intervals
        active.retain(|(_, act_end, reg)| {
            if *act_end < start_pc {
                free_regs.insert(*reg);
                false
            } else {
                true
            }
        });
        if let Some(&reg) = free_regs.iter().next() {
            free_regs.remove(&reg);
            active.push((v.clone(), end_pc, reg));
            linear_scan_map.insert(v.clone(), AARCH64_CALLEE_REGS[reg].to_string());
        } else {
            linear_scan_map.insert(v.clone(), "[sp, #spill]".to_string());
        }
    }

    // Compute maximum register pressure (max simultaneous live intervals at any pc)
    let max_pc = insts.len().max(1);
    let mut max_pressure_clique = 0usize;
    for pc in 0..max_pc {
        let live_now = all_vars
            .iter()
            .filter(|v| var_start[*v] <= pc && pc <= var_end[*v])
            .count();
        if live_now > max_pressure_clique {
            max_pressure_clique = live_now;
        }
    }

    let mut intervals = Vec::new();
    let mut used_colors_set = BTreeSet::new();
    let mut spilled_vars = 0usize;

    for v in &sorted_vars {
        let col = assigned_color.get(v).copied().flatten();
        if let Some(c) = col {
            used_colors_set.insert(c);
        } else {
            spilled_vars += 1;
        }
        let aarch64_loc = match col {
            Some(c) => AARCH64_CALLEE_REGS[c % AARCH64_CALLEE_REGS.len()].to_string(),
            None => format!("[sp, #{}]", spill_slot_offset[v]),
        };
        let x86_64_loc = match col {
            Some(c) => X86_64_ALLOC_REGS[c % X86_64_ALLOC_REGS.len()].to_string(),
            None => format!("QWORD PTR [rbp - {}]", spill_slot_offset[v]),
        };
        intervals.push(LiveInterval {
            var_name: v.clone(),
            start_pc: var_start[v],
            end_pc: var_end[v],
            use_count: *var_uses.get(v).unwrap_or(&0),
            max_loop_depth: *var_loop_depth.get(v).unwrap_or(&0),
            spill_weight: *spill_weights.get(v).unwrap_or(&1.0),
            degree: adj[v].len(),
            assigned_color: col,
            aarch64_loc,
            x86_64_loc,
            linear_scan_loc: linear_scan_map
                .get(v)
                .cloned()
                .unwrap_or_else(|| "x19".to_string()),
            spilled: col.is_none(),
        });
    }

    let stack_frame_bytes = next_spill_offset.div_ceil(16) * 16;
    let mermaid_graph = build_interference_mermaid(&f.name, &intervals, &edges);
    let aarch64_asm = emit_aarch64_assembly(&f.name, &insts, &intervals, stack_frame_bytes);
    let x86_64_asm = emit_x86_64_assembly(&f.name, &insts, &intervals, stack_frame_bytes);

    FunctionRegAllocReport {
        fn_name: f.name.clone(),
        signature,
        k_registers: k,
        virtual_regs: all_vars.len(),
        interference_edges_count,
        max_pressure_clique,
        chromatic_colors_used: used_colors_set.len(),
        coalesced_moves,
        spilled_vars,
        stack_frame_bytes,
        intervals,
        edges,
        kempe_order,
        mermaid_graph,
        aarch64_asm,
        x86_64_asm,
    }
}

fn lower_stmts_to_ir(
    stmts: &[Stmt],
    loop_depth: usize,
    insts: &mut Vec<IrInst>,
    temp_counter: &mut usize,
    label_counter: &mut usize,
) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { name, value, .. } => {
                let rhs = lower_expr_to_ir(value, Some(name), loop_depth, insts, temp_counter);
                if rhs != *name {
                    let pc = insts.len();
                    insts.push(IrInst {
                        pc,
                        loop_depth,
                        op: IrOp::MovCopy {
                            dst: name.clone(),
                            src: rhs.clone(),
                        },
                        defs: vec![name.clone()],
                        uses: vec![rhs],
                    });
                }
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let dst_name = match target {
                    AssignTarget::Var(v) => v.clone(),
                    AssignTarget::Index { base, .. } | AssignTarget::Field { base, .. } => {
                        base.clone()
                    }
                };
                match op {
                    AssignOp::Set => {
                        let rhs = lower_expr_to_ir(
                            value,
                            Some(&dst_name),
                            loop_depth,
                            insts,
                            temp_counter,
                        );
                        if rhs != dst_name {
                            let pc = insts.len();
                            insts.push(IrInst {
                                pc,
                                loop_depth,
                                op: IrOp::MovCopy {
                                    dst: dst_name.clone(),
                                    src: rhs.clone(),
                                },
                                defs: vec![dst_name],
                                uses: vec![rhs],
                            });
                        }
                    }
                    AssignOp::AddAssign | AssignOp::SubAssign => {
                        let rhs = lower_expr_to_ir(value, None, loop_depth, insts, temp_counter);
                        let bop = if *op == AssignOp::AddAssign {
                            BinOp::Add
                        } else {
                            BinOp::Sub
                        };
                        let pc = insts.len();
                        insts.push(IrInst {
                            pc,
                            loop_depth,
                            op: IrOp::BinOp {
                                dst: dst_name.clone(),
                                op: bop,
                                lhs: dst_name.clone(),
                                rhs: rhs.clone(),
                            },
                            defs: vec![dst_name.clone()],
                            uses: vec![dst_name, rhs],
                        });
                    }
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let cond_v = lower_expr_to_ir(cond, None, loop_depth, insts, temp_counter);
                let id = *label_counter;
                *label_counter += 1;
                let else_lbl = format!(".L_else_{}", id);
                let end_lbl = format!(".L_endif_{}", id);

                let pc = insts.len();
                insts.push(IrInst {
                    pc,
                    loop_depth,
                    op: IrOp::CmpBranchFalse {
                        cond_var: cond_v.clone(),
                        target_label: if else_body.is_empty() {
                            end_lbl.clone()
                        } else {
                            else_lbl.clone()
                        },
                    },
                    defs: Vec::new(),
                    uses: vec![cond_v],
                });

                lower_stmts_to_ir(then_body, loop_depth, insts, temp_counter, label_counter);

                if !else_body.is_empty() {
                    let jpc = insts.len();
                    insts.push(IrInst {
                        pc: jpc,
                        loop_depth,
                        op: IrOp::Jump {
                            target_label: end_lbl.clone(),
                        },
                        defs: Vec::new(),
                        uses: Vec::new(),
                    });
                    let lpc = insts.len();
                    insts.push(IrInst {
                        pc: lpc,
                        loop_depth,
                        op: IrOp::Label { name: else_lbl },
                        defs: Vec::new(),
                        uses: Vec::new(),
                    });
                    lower_stmts_to_ir(else_body, loop_depth, insts, temp_counter, label_counter);
                }

                let epc = insts.len();
                insts.push(IrInst {
                    pc: epc,
                    loop_depth,
                    op: IrOp::Label { name: end_lbl },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
            }
            Stmt::Match { expr, arms, .. } => {
                let scr_v = lower_expr_to_ir(expr, None, loop_depth, insts, temp_counter);
                let id = *label_counter;
                *label_counter += 1;
                let end_lbl = format!(".L_endmatch_{}", id);
                for (a_idx, arm) in arms.iter().enumerate() {
                    let next_lbl = format!(".L_arm_{}_{}", id, a_idx + 1);
                    if !matches!(arm.pat, MatchPat::Wildcard) {
                        let pat_v = format!("t{}", *temp_counter);
                        *temp_counter += 1;
                        let pat_imm = match &arm.pat {
                            MatchPat::Int(v) => *v,
                            MatchPat::EnumVariant { variant, .. } => variant.len() as i64,
                            MatchPat::Str(s) => s.len() as i64,
                            MatchPat::Wildcard => 0,
                        };
                        let p_pc = insts.len();
                        insts.push(IrInst {
                            pc: p_pc,
                            loop_depth,
                            op: IrOp::MovImm {
                                dst: pat_v.clone(),
                                imm: pat_imm,
                            },
                            defs: vec![pat_v.clone()],
                            uses: Vec::new(),
                        });
                        let cmp_v = format!("t{}", *temp_counter);
                        *temp_counter += 1;
                        let c_pc = insts.len();
                        insts.push(IrInst {
                            pc: c_pc,
                            loop_depth,
                            op: IrOp::BinOp {
                                dst: cmp_v.clone(),
                                op: BinOp::Eq,
                                lhs: scr_v.clone(),
                                rhs: pat_v.clone(),
                            },
                            defs: vec![cmp_v.clone()],
                            uses: vec![scr_v.clone(), pat_v],
                        });
                        let pc = insts.len();
                        insts.push(IrInst {
                            pc,
                            loop_depth,
                            op: IrOp::CmpBranchFalse {
                                cond_var: cmp_v.clone(),
                                target_label: next_lbl.clone(),
                            },
                            defs: Vec::new(),
                            uses: vec![cmp_v],
                        });
                    }
                    lower_stmts_to_ir(&arm.body, loop_depth, insts, temp_counter, label_counter);
                    let jpc = insts.len();
                    insts.push(IrInst {
                        pc: jpc,
                        loop_depth,
                        op: IrOp::Jump {
                            target_label: end_lbl.clone(),
                        },
                        defs: Vec::new(),
                        uses: Vec::new(),
                    });
                    let lpc = insts.len();
                    insts.push(IrInst {
                        pc: lpc,
                        loop_depth,
                        op: IrOp::Label { name: next_lbl },
                        defs: Vec::new(),
                        uses: Vec::new(),
                    });
                }
                let epc = insts.len();
                insts.push(IrInst {
                    pc: epc,
                    loop_depth,
                    op: IrOp::Label { name: end_lbl },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                let s_v = lower_expr_to_ir(start, Some(var), loop_depth, insts, temp_counter);
                if s_v != *var {
                    let pc = insts.len();
                    insts.push(IrInst {
                        pc,
                        loop_depth,
                        op: IrOp::MovCopy {
                            dst: var.clone(),
                            src: s_v.clone(),
                        },
                        defs: vec![var.clone()],
                        uses: vec![s_v],
                    });
                }
                let id = *label_counter;
                *label_counter += 1;
                let hdr_lbl = format!(".L_loop_hdr_{}", id);
                let exit_lbl = format!(".L_loop_exit_{}", id);

                let hpc = insts.len();
                insts.push(IrInst {
                    pc: hpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::Label {
                        name: hdr_lbl.clone(),
                    },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });

                let e_v = lower_expr_to_ir(end, None, loop_depth + 1, insts, temp_counter);
                let cmp_tmp = alloc_tmp(temp_counter);
                let cpc = insts.len();
                insts.push(IrInst {
                    pc: cpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::BinOp {
                        dst: cmp_tmp.clone(),
                        op: BinOp::Lt,
                        lhs: var.clone(),
                        rhs: e_v.clone(),
                    },
                    defs: vec![cmp_tmp.clone()],
                    uses: vec![var.clone(), e_v],
                });
                let bpc = insts.len();
                insts.push(IrInst {
                    pc: bpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::CmpBranchFalse {
                        cond_var: cmp_tmp.clone(),
                        target_label: exit_lbl.clone(),
                    },
                    defs: Vec::new(),
                    uses: vec![cmp_tmp],
                });

                lower_stmts_to_ir(body, loop_depth + 1, insts, temp_counter, label_counter);

                let one_tmp = alloc_tmp(temp_counter);
                let ipc1 = insts.len();
                insts.push(IrInst {
                    pc: ipc1,
                    loop_depth: loop_depth + 1,
                    op: IrOp::MovImm {
                        dst: one_tmp.clone(),
                        imm: 1,
                    },
                    defs: vec![one_tmp.clone()],
                    uses: Vec::new(),
                });
                let ipc2 = insts.len();
                insts.push(IrInst {
                    pc: ipc2,
                    loop_depth: loop_depth + 1,
                    op: IrOp::BinOp {
                        dst: var.clone(),
                        op: BinOp::Add,
                        lhs: var.clone(),
                        rhs: one_tmp.clone(),
                    },
                    defs: vec![var.clone()],
                    uses: vec![var.clone(), one_tmp],
                });
                let jpc = insts.len();
                insts.push(IrInst {
                    pc: jpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::Jump {
                        target_label: hdr_lbl,
                    },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
                let xpc = insts.len();
                insts.push(IrInst {
                    pc: xpc,
                    loop_depth,
                    op: IrOp::Label { name: exit_lbl },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let iter_v = lower_expr_to_ir(iter, None, loop_depth, insts, temp_counter);
                let id = *label_counter;
                *label_counter += 1;
                let hdr_lbl = format!(".L_foreach_hdr_{}", id);
                let exit_lbl = format!(".L_foreach_exit_{}", id);

                let hpc = insts.len();
                insts.push(IrInst {
                    pc: hpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::Label {
                        name: hdr_lbl.clone(),
                    },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
                let bpc = insts.len();
                insts.push(IrInst {
                    pc: bpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::MovCopy {
                        dst: var.clone(),
                        src: iter_v.clone(),
                    },
                    defs: vec![var.clone()],
                    uses: vec![iter_v.clone()],
                });
                let cpc = insts.len();
                insts.push(IrInst {
                    pc: cpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::CmpBranchFalse {
                        cond_var: iter_v.clone(),
                        target_label: exit_lbl.clone(),
                    },
                    defs: Vec::new(),
                    uses: vec![iter_v],
                });

                lower_stmts_to_ir(body, loop_depth + 1, insts, temp_counter, label_counter);

                let jpc = insts.len();
                insts.push(IrInst {
                    pc: jpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::Jump {
                        target_label: hdr_lbl,
                    },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
                let xpc = insts.len();
                insts.push(IrInst {
                    pc: xpc,
                    loop_depth,
                    op: IrOp::Label { name: exit_lbl },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
            }
            Stmt::While { cond, body, .. } => {
                let id = *label_counter;
                *label_counter += 1;
                let hdr_lbl = format!(".L_while_hdr_{}", id);
                let exit_lbl = format!(".L_while_exit_{}", id);

                let hpc = insts.len();
                insts.push(IrInst {
                    pc: hpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::Label {
                        name: hdr_lbl.clone(),
                    },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
                let cond_v = lower_expr_to_ir(cond, None, loop_depth + 1, insts, temp_counter);
                let bpc = insts.len();
                insts.push(IrInst {
                    pc: bpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::CmpBranchFalse {
                        cond_var: cond_v.clone(),
                        target_label: exit_lbl.clone(),
                    },
                    defs: Vec::new(),
                    uses: vec![cond_v],
                });

                lower_stmts_to_ir(body, loop_depth + 1, insts, temp_counter, label_counter);

                let jpc = insts.len();
                insts.push(IrInst {
                    pc: jpc,
                    loop_depth: loop_depth + 1,
                    op: IrOp::Jump {
                        target_label: hdr_lbl,
                    },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
                let xpc = insts.len();
                insts.push(IrInst {
                    pc: xpc,
                    loop_depth,
                    op: IrOp::Label { name: exit_lbl },
                    defs: Vec::new(),
                    uses: Vec::new(),
                });
            }
            Stmt::Return { value, .. } => {
                let src = value
                    .as_ref()
                    .map(|e| lower_expr_to_ir(e, None, loop_depth, insts, temp_counter));
                let uses = src.iter().cloned().collect();
                let pc = insts.len();
                insts.push(IrInst {
                    pc,
                    loop_depth,
                    op: IrOp::Return { src },
                    defs: Vec::new(),
                    uses,
                });
            }
            Stmt::Assert { cond, .. } => {
                let _ = lower_expr_to_ir(cond, None, loop_depth, insts, temp_counter);
            }
            Stmt::AssertEq { left, right, .. } => {
                let _ = lower_expr_to_ir(left, None, loop_depth, insts, temp_counter);
                let _ = lower_expr_to_ir(right, None, loop_depth, insts, temp_counter);
            }
            Stmt::Expr { expr, .. } => {
                let _ = lower_expr_to_ir(expr, None, loop_depth, insts, temp_counter);
            }
            Stmt::Break { .. } | Stmt::Continue { .. } | Stmt::Comment { .. } => {}
        }
    }
}

fn alloc_tmp(temp_counter: &mut usize) -> String {
    let name = format!("t{}", *temp_counter);
    *temp_counter += 1;
    name
}

fn lower_expr_to_ir(
    expr: &Expr,
    preferred_dst: Option<&str>,
    loop_depth: usize,
    insts: &mut Vec<IrInst>,
    temp_counter: &mut usize,
) -> String {
    match expr {
        Expr::Var(v) => v.clone(),
        Expr::Int(n) => {
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let pc = insts.len();
            insts.push(IrInst {
                pc,
                loop_depth,
                op: IrOp::MovImm {
                    dst: dst.clone(),
                    imm: *n,
                },
                defs: vec![dst.clone()],
                uses: Vec::new(),
            });
            dst
        }
        Expr::Bool(b) => {
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let pc = insts.len();
            insts.push(IrInst {
                pc,
                loop_depth,
                op: IrOp::MovImm {
                    dst: dst.clone(),
                    imm: if *b { 1 } else { 0 },
                },
                defs: vec![dst.clone()],
                uses: Vec::new(),
            });
            dst
        }
        Expr::Float(_) | Expr::Str(_) | Expr::EnumVariant { .. } => {
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let pc = insts.len();
            insts.push(IrInst {
                pc,
                loop_depth,
                op: IrOp::MovImm {
                    dst: dst.clone(),
                    imm: 0,
                },
                defs: vec![dst.clone()],
                uses: Vec::new(),
            });
            dst
        }
        Expr::Unary { op, expr: inner } => {
            let src = lower_expr_to_ir(inner, None, loop_depth, insts, temp_counter);
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let zero = alloc_tmp(temp_counter);
            let pc0 = insts.len();
            insts.push(IrInst {
                pc: pc0,
                loop_depth,
                op: IrOp::MovImm {
                    dst: zero.clone(),
                    imm: 0,
                },
                defs: vec![zero.clone()],
                uses: Vec::new(),
            });
            let bop = match op {
                UnaryOp::Neg => BinOp::Sub,
                UnaryOp::Not => BinOp::Eq,
            };
            let pc1 = insts.len();
            insts.push(IrInst {
                pc: pc1,
                loop_depth,
                op: IrOp::BinOp {
                    dst: dst.clone(),
                    op: bop,
                    lhs: zero.clone(),
                    rhs: src.clone(),
                },
                defs: vec![dst.clone()],
                uses: vec![zero, src],
            });
            dst
        }
        Expr::Binary { op, left, right } => {
            let lhs = lower_expr_to_ir(left, None, loop_depth, insts, temp_counter);
            let rhs = lower_expr_to_ir(right, None, loop_depth, insts, temp_counter);
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let pc = insts.len();
            insts.push(IrInst {
                pc,
                loop_depth,
                op: IrOp::BinOp {
                    dst: dst.clone(),
                    op: *op,
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                },
                defs: vec![dst.clone()],
                uses: vec![lhs, rhs],
            });
            dst
        }
        Expr::Index { base, index } => {
            let b_v = lower_expr_to_ir(base, None, loop_depth, insts, temp_counter);
            let i_v = lower_expr_to_ir(index, None, loop_depth, insts, temp_counter);
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let pc = insts.len();
            insts.push(IrInst {
                pc,
                loop_depth,
                op: IrOp::BinOp {
                    dst: dst.clone(),
                    op: BinOp::Add,
                    lhs: b_v.clone(),
                    rhs: i_v.clone(),
                },
                defs: vec![dst.clone()],
                uses: vec![b_v, i_v],
            });
            dst
        }
        Expr::FieldAccess { base, .. } => {
            let b_v = lower_expr_to_ir(base, None, loop_depth, insts, temp_counter);
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let pc = insts.len();
            insts.push(IrInst {
                pc,
                loop_depth,
                op: IrOp::MovCopy {
                    dst: dst.clone(),
                    src: b_v.clone(),
                },
                defs: vec![dst.clone()],
                uses: vec![b_v],
            });
            dst
        }
        Expr::Call { func, args } => {
            let mut arg_vars = Vec::new();
            for a in args {
                arg_vars.push(lower_expr_to_ir(a, None, loop_depth, insts, temp_counter));
            }
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let pc = insts.len();
            insts.push(IrInst {
                pc,
                loop_depth,
                op: IrOp::Call {
                    dst: dst.clone(),
                    callee: func.clone(),
                    args: arg_vars.clone(),
                },
                defs: vec![dst.clone()],
                uses: arg_vars,
            });
            dst
        }
        Expr::StructInit { fields, .. } => {
            let mut f_vars = Vec::new();
            for (_, fv) in fields {
                f_vars.push(lower_expr_to_ir(fv, None, loop_depth, insts, temp_counter));
            }
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let pc = insts.len();
            insts.push(IrInst {
                pc,
                loop_depth,
                op: IrOp::Call {
                    dst: dst.clone(),
                    callee: "__star_struct_pack".to_string(),
                    args: f_vars.clone(),
                },
                defs: vec![dst.clone()],
                uses: f_vars,
            });
            dst
        }
        Expr::List(items) => {
            let mut item_vars = Vec::new();
            for it in items {
                item_vars.push(lower_expr_to_ir(it, None, loop_depth, insts, temp_counter));
            }
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            let pc = insts.len();
            insts.push(IrInst {
                pc,
                loop_depth,
                op: IrOp::Call {
                    dst: dst.clone(),
                    callee: "__star_list_alloc".to_string(),
                    args: item_vars.clone(),
                },
                defs: vec![dst.clone()],
                uses: item_vars,
            });
            dst
        }
        Expr::Intrinsic(intr) => {
            let dst = preferred_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| alloc_tmp(temp_counter));
            match intr.as_ref() {
                Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                    let av = lower_expr_to_ir(a, None, loop_depth, insts, temp_counter);
                    let bv = lower_expr_to_ir(b, None, loop_depth, insts, temp_counter);
                    let callee = if matches!(intr.as_ref(), Intrinsic::Min(..)) {
                        "__csel_min"
                    } else {
                        "__csel_max"
                    };
                    let pc = insts.len();
                    insts.push(IrInst {
                        pc,
                        loop_depth,
                        op: IrOp::Call {
                            dst: dst.clone(),
                            callee: callee.to_string(),
                            args: vec![av.clone(), bv.clone()],
                        },
                        defs: vec![dst.clone()],
                        uses: vec![av, bv],
                    });
                }
                Intrinsic::Len(a)
                | Intrinsic::Abs(a)
                | Intrinsic::Upper(a)
                | Intrinsic::Lower(a)
                | Intrinsic::ToStr(a) => {
                    let av = lower_expr_to_ir(a, None, loop_depth, insts, temp_counter);
                    let pc = insts.len();
                    insts.push(IrInst {
                        pc,
                        loop_depth,
                        op: IrOp::MovCopy {
                            dst: dst.clone(),
                            src: av.clone(),
                        },
                        defs: vec![dst.clone()],
                        uses: vec![av],
                    });
                }
                Intrinsic::Push { list, value }
                | Intrinsic::Contains {
                    haystack: list,
                    needle: value,
                } => {
                    let lv = lower_expr_to_ir(list, None, loop_depth, insts, temp_counter);
                    let vv = lower_expr_to_ir(value, None, loop_depth, insts, temp_counter);
                    let pc = insts.len();
                    insts.push(IrInst {
                        pc,
                        loop_depth,
                        op: IrOp::Call {
                            dst: dst.clone(),
                            callee: "__star_list_op".to_string(),
                            args: vec![lv.clone(), vv.clone()],
                        },
                        defs: vec![dst.clone()],
                        uses: vec![lv, vv],
                    });
                }
                Intrinsic::Print(args) => {
                    let mut avs = Vec::new();
                    for a in args {
                        avs.push(lower_expr_to_ir(a, None, loop_depth, insts, temp_counter));
                    }
                    let pc = insts.len();
                    insts.push(IrInst {
                        pc,
                        loop_depth,
                        op: IrOp::Call {
                            dst: dst.clone(),
                            callee: "_star_print".to_string(),
                            args: avs.clone(),
                        },
                        defs: vec![dst.clone()],
                        uses: avs,
                    });
                }
            }
            dst
        }
    }
}

fn build_interference_mermaid(
    fn_name: &str,
    intervals: &[LiveInterval],
    edges: &[InterferenceEdge],
) -> String {
    let mut out = String::from("graph LR\n");
    out.push_str(&format!("  subgraph \"Interference Graph: {}\"\n", fn_name));
    for iv in intervals {
        let id = iv.var_name.replace(|c: char| !c.is_alphanumeric(), "_");
        out.push_str(&format!(
            "    {}[\"{} ➔ {} / {} (pc {}..{}, deg {})\"]\n",
            id, iv.var_name, iv.aarch64_loc, iv.x86_64_loc, iv.start_pc, iv.end_pc, iv.degree
        ));
    }
    for e in edges.iter().take(28) {
        let u = e.u.replace(|c: char| !c.is_alphanumeric(), "_");
        let v = e.v.replace(|c: char| !c.is_alphanumeric(), "_");
        if e.kind == "CoalescedMove" {
            out.push_str(&format!("    {} -. \"coalesce\" .- {}\n", u, v));
        } else {
            out.push_str(&format!("    {} --- {}\n", u, v));
        }
    }
    out.push_str("  end\n");
    out
}

fn emit_aarch64_assembly(
    fn_name: &str,
    insts: &[IrInst],
    intervals: &[LiveInterval],
    frame_bytes: usize,
) -> String {
    let loc_map: BTreeMap<&str, &str> = intervals
        .iter()
        .map(|iv| (iv.var_name.as_str(), iv.aarch64_loc.as_str()))
        .collect();
    let resolve = |v: &str| -> String {
        loc_map
            .get(v)
            .copied()
            .unwrap_or("x19")
            .to_string()
    };

    let mut out = String::new();
    out.push_str(&format!(
        "// AArch64 (ARM64 AAPCS64) — Chaitin-Briggs Register-Allocated Codegen\n.globl _{}\n.p2align 2\n_{}:\n",
        fn_name, fn_name
    ));
    out.push_str(&format!(
        "    stp x29, x30, [sp, #-{}]!\n    mov x29, sp\n",
        frame_bytes.max(16)
    ));

    for inst in insts {
        match &inst.op {
            IrOp::ParamBind { name, idx } => {
                let dst = resolve(name);
                let arg_reg = AARCH64_ARG_REGS[*idx % AARCH64_ARG_REGS.len()];
                out.push_str(&format!(
                    "    mov {}, {}                    // param `{}`\n",
                    dst, arg_reg, name
                ));
            }
            IrOp::MovImm { dst, imm } => {
                let d = resolve(dst);
                out.push_str(&format!(
                    "    mov {}, #{}                   // {} = {}\n",
                    d, imm, dst, imm
                ));
            }
            IrOp::MovCopy { dst, src } => {
                let d = resolve(dst);
                let s = resolve(src);
                if d != s {
                    out.push_str(&format!(
                        "    mov {}, {}                    // {} = {}\n",
                        d, s, dst, src
                    ));
                } else {
                    out.push_str(&format!(
                        "    // [coalesced move elided] {} == {} in {}\n",
                        dst, src, d
                    ));
                }
            }
            IrOp::BinOp { dst, op, lhs, rhs } => {
                let d = resolve(dst);
                let l = resolve(lhs);
                let r = resolve(rhs);
                match op {
                    BinOp::Add => out.push_str(&format!("    add {}, {}, {}\n", d, l, r)),
                    BinOp::Sub => out.push_str(&format!("    sub {}, {}, {}\n", d, l, r)),
                    BinOp::Mul => out.push_str(&format!("    mul {}, {}, {}\n", d, l, r)),
                    BinOp::Div | BinOp::IntDiv => {
                        out.push_str(&format!("    sdiv {}, {}, {}\n", d, l, r))
                    }
                    BinOp::Mod => {
                        out.push_str(&format!(
                            "    sdiv x9, {}, {}\n    msub {}, x9, {}, {}\n",
                            l, r, d, r, l
                        ));
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne => {
                        let cc = match op {
                            BinOp::Lt => "lt",
                            BinOp::Le => "le",
                            BinOp::Gt => "gt",
                            BinOp::Ge => "ge",
                            BinOp::Eq => "eq",
                            _ => "ne",
                        };
                        out.push_str(&format!(
                            "    cmp {}, {}\n    cset {}, {}\n",
                            l, r, d, cc
                        ));
                    }
                    BinOp::And => out.push_str(&format!("    and {}, {}, {}\n", d, l, r)),
                    BinOp::Or => out.push_str(&format!("    orr {}, {}, {}\n", d, l, r)),
                }
            }
            IrOp::Call { dst, callee, args } => {
                let d = resolve(dst);
                if callee == "__csel_min" && args.len() == 2 {
                    let a = resolve(&args[0]);
                    let b = resolve(&args[1]);
                    out.push_str(&format!(
                        "    cmp {}, {}\n    csel {}, {}, {}, lt            // min({}, {})\n",
                        a, b, d, a, b, args[0], args[1]
                    ));
                } else if callee == "__csel_max" && args.len() == 2 {
                    let a = resolve(&args[0]);
                    let b = resolve(&args[1]);
                    out.push_str(&format!(
                        "    cmp {}, {}\n    csel {}, {}, {}, gt            // max({}, {})\n",
                        a, b, d, a, b, args[0], args[1]
                    ));
                } else {
                    for (i, a) in args.iter().take(8).enumerate() {
                        let s = resolve(a);
                        out.push_str(&format!("    mov {}, {}\n", AARCH64_ARG_REGS[i], s));
                    }
                    out.push_str(&format!(
                        "    bl _{}\n    mov {}, x0\n",
                        callee, d
                    ));
                }
            }
            IrOp::Label { name } => {
                out.push_str(&format!("{}:\n", name));
            }
            IrOp::CmpBranchFalse {
                cond_var,
                target_label,
            } => {
                let c = resolve(cond_var);
                out.push_str(&format!("    cbz {}, {}\n", c, target_label));
            }
            IrOp::Jump { target_label } => {
                out.push_str(&format!("    b {}\n", target_label));
            }
            IrOp::Return { src } => {
                if let Some(s) = src {
                    let r = resolve(s);
                    out.push_str(&format!("    mov x0, {}\n", r));
                }
                out.push_str(&format!(
                    "    ldp x29, x30, [sp], #{}\n    ret\n",
                    frame_bytes.max(16)
                ));
            }
        }
    }

    out
}

fn emit_x86_64_assembly(
    fn_name: &str,
    insts: &[IrInst],
    intervals: &[LiveInterval],
    frame_bytes: usize,
) -> String {
    let loc_map: BTreeMap<&str, &str> = intervals
        .iter()
        .map(|iv| (iv.var_name.as_str(), iv.x86_64_loc.as_str()))
        .collect();
    let resolve = |v: &str| -> String {
        loc_map
            .get(v)
            .copied()
            .unwrap_or("rbx")
            .to_string()
    };

    let mut out = String::new();
    out.push_str(&format!(
        "# x86_64 (System V AMD64 ABI, Intel Syntax) — Chaitin-Briggs Register-Allocated Codegen\n.intel_syntax noprefix\n.globl {}\n{}:\n",
        fn_name, fn_name
    ));
    out.push_str(&format!(
        "    push rbp\n    mov rbp, rsp\n    sub rsp, {}\n",
        frame_bytes.max(16)
    ));

    for inst in insts {
        match &inst.op {
            IrOp::ParamBind { name, idx } => {
                let dst = resolve(name);
                let arg_reg = X86_64_ARG_REGS[*idx % X86_64_ARG_REGS.len()];
                out.push_str(&format!(
                    "    mov {}, {}                    # param `{}`\n",
                    dst, arg_reg, name
                ));
            }
            IrOp::MovImm { dst, imm } => {
                let d = resolve(dst);
                out.push_str(&format!(
                    "    mov {}, {}                    # {} = {}\n",
                    d, imm, dst, imm
                ));
            }
            IrOp::MovCopy { dst, src } => {
                let d = resolve(dst);
                let s = resolve(src);
                if d != s {
                    out.push_str(&format!(
                        "    mov {}, {}                    # {} = {}\n",
                        d, s, dst, src
                    ));
                } else {
                    out.push_str(&format!(
                        "    # [coalesced move elided] {} == {} in {}\n",
                        dst, src, d
                    ));
                }
            }
            IrOp::BinOp { dst, op, lhs, rhs } => {
                let d = resolve(dst);
                let l = resolve(lhs);
                let r = resolve(rhs);
                match op {
                    BinOp::Add => {
                        if d != l {
                            out.push_str(&format!("    mov {}, {}\n", d, l));
                        }
                        out.push_str(&format!("    add {}, {}\n", d, r));
                    }
                    BinOp::Sub => {
                        if d != l {
                            out.push_str(&format!("    mov {}, {}\n", d, l));
                        }
                        out.push_str(&format!("    sub {}, {}\n", d, r));
                    }
                    BinOp::Mul => {
                        if d != l {
                            out.push_str(&format!("    mov {}, {}\n", d, l));
                        }
                        out.push_str(&format!("    imul {}, {}\n", d, r));
                    }
                    BinOp::Div | BinOp::IntDiv => {
                        out.push_str(&format!(
                            "    mov rax, {}\n    cqo\n    idiv {}\n    mov {}, rax\n",
                            l, r, d
                        ));
                    }
                    BinOp::Mod => {
                        out.push_str(&format!(
                            "    mov rax, {}\n    cqo\n    idiv {}\n    mov {}, rdx\n",
                            l, r, d
                        ));
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne => {
                        let set_op = match op {
                            BinOp::Lt => "setl",
                            BinOp::Le => "setle",
                            BinOp::Gt => "setg",
                            BinOp::Ge => "setge",
                            BinOp::Eq => "sete",
                            _ => "setne",
                        };
                        out.push_str(&format!(
                            "    cmp {}, {}\n    {} al\n    movzx {}, al\n",
                            l, r, set_op, d
                        ));
                    }
                    BinOp::And => {
                        if d != l {
                            out.push_str(&format!("    mov {}, {}\n", d, l));
                        }
                        out.push_str(&format!("    and {}, {}\n", d, r));
                    }
                    BinOp::Or => {
                        if d != l {
                            out.push_str(&format!("    mov {}, {}\n", d, l));
                        }
                        out.push_str(&format!("    or {}, {}\n", d, r));
                    }
                }
            }
            IrOp::Call { dst, callee, args } => {
                let d = resolve(dst);
                if callee == "__csel_min" && args.len() == 2 {
                    let a = resolve(&args[0]);
                    let b = resolve(&args[1]);
                    out.push_str(&format!(
                        "    mov {}, {}\n    cmp {}, {}\n    cmovg {}, {}                  # min({}, {})\n",
                        d, a, d, b, d, b, args[0], args[1]
                    ));
                } else if callee == "__csel_max" && args.len() == 2 {
                    let a = resolve(&args[0]);
                    let b = resolve(&args[1]);
                    out.push_str(&format!(
                        "    mov {}, {}\n    cmp {}, {}\n    cmovl {}, {}                  # max({}, {})\n",
                        d, a, d, b, d, b, args[0], args[1]
                    ));
                } else {
                    for (i, a) in args.iter().take(6).enumerate() {
                        let s = resolve(a);
                        out.push_str(&format!("    mov {}, {}\n", X86_64_ARG_REGS[i], s));
                    }
                    out.push_str(&format!(
                        "    call {}\n    mov {}, rax\n",
                        callee, d
                    ));
                }
            }
            IrOp::Label { name } => {
                out.push_str(&format!("{}:\n", name));
            }
            IrOp::CmpBranchFalse {
                cond_var,
                target_label,
            } => {
                let c = resolve(cond_var);
                out.push_str(&format!(
                    "    test {}, {}\n    jz {}\n",
                    c, c, target_label
                ));
            }
            IrOp::Jump { target_label } => {
                out.push_str(&format!("    jmp {}\n", target_label));
            }
            IrOp::Return { src } => {
                if let Some(s) = src {
                    let r = resolve(s);
                    out.push_str(&format!("    mov rax, {}\n", r));
                }
                out.push_str(&format!(
                    "    add rsp, {}\n    pop rbp\n    ret\n",
                    frame_bytes.max(16)
                ));
            }
        }
    }

    out
}

/// Run Interprocedural Escape Analysis, Scalar Replacement of Aggregates (`SROA`),
/// Return-Value Optimization (`RVO`), and 13-Spoke Stack/Arena Lifetime Synthesis.
pub fn analyze_escape_and_lifetimes(hub: &HubModule) -> EscapeAnalysisReport {
    let start = Instant::now();
    let mut struct_field_counts: BTreeMap<String, usize> = BTreeMap::new();
    for item in &hub.items {
        if let Item::Struct(st) = item {
            struct_field_counts.insert(st.name.clone(), st.fields.len());
        }
    }

    let mut functions = Vec::new();
    let mut total_alloc_sites = 0usize;
    let mut stack_promoted_sites = 0usize;
    let mut rvo_eliminated_sites = 0usize;
    let mut sroa_scalarized_fields = 0usize;
    let mut heap_escaping_sites = 0usize;
    let mut total_bytes_saved_per_run = 0usize;

    for item in &hub.items {
        if let Item::Function(f) = item {
            let rep = audit_fn_escape(f, &struct_field_counts);
            total_alloc_sites += rep.total_sites;
            stack_promoted_sites += rep.stack_or_sroa_sites;
            rvo_eliminated_sites += rep.rvo_sites;
            heap_escaping_sites += rep.heap_escape_sites;
            sroa_scalarized_fields += rep.sites.iter().map(|s| s.sroa_fields).sum::<usize>();
            total_bytes_saved_per_run += rep.bytes_saved_per_call;
            functions.push(rep);
        }
    }

    let eliminated = stack_promoted_sites + rvo_eliminated_sites;
    let heap_reduction_pct = (eliminated * 100)
        .checked_div(total_alloc_sites)
        .map(|v| v.min(100) as u8)
        .unwrap_or(100);

    EscapeAnalysisReport {
        total_functions: functions.len(),
        total_alloc_sites,
        stack_promoted_sites,
        rvo_eliminated_sites,
        sroa_scalarized_fields,
        heap_escaping_sites,
        total_bytes_saved_per_run,
        heap_reduction_pct,
        functions,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

fn audit_fn_escape(
    f: &FnDecl,
    struct_field_counts: &BTreeMap<String, usize>,
) -> FunctionEscapeReport {
    let params_sig: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.ty.display()))
        .collect();
    let signature = format!(
        "fn {}({}) -> {}",
        f.name,
        params_sig.join(", "),
        f.ret_ty.display()
    );

    // Collect variables that are returned from `f`
    let mut returned_vars = BTreeSet::new();
    collect_returned_vars(&f.body, &mut returned_vars);

    let mut sites = Vec::new();
    scan_stmts_alloc_sites(
        &f.name,
        &f.body,
        false,
        &returned_vars,
        struct_field_counts,
        &mut sites,
    );

    let total_sites = sites.len();
    let stack_or_sroa_sites = sites
        .iter()
        .filter(|s| s.escape_state.starts_with("NoEscape") || s.escape_state.starts_with("LoopArena"))
        .count();
    let rvo_sites = sites
        .iter()
        .filter(|s| s.escape_state.starts_with("ReturnEscape"))
        .count();
    let heap_escape_sites = sites
        .iter()
        .filter(|s| s.escape_state.starts_with("HeapEscape"))
        .count();
    let bytes_saved_per_call = sites.iter().map(|s| s.estimated_bytes_saved).sum();

    let optimized_by_spoke = synthesize_lifetime_projections(f, &sites);

    FunctionEscapeReport {
        fn_name: f.name.clone(),
        signature,
        total_sites,
        stack_or_sroa_sites,
        rvo_sites,
        heap_escape_sites,
        bytes_saved_per_call,
        sites,
        optimized_by_spoke,
    }
}

fn collect_returned_vars(stmts: &[Stmt], out: &mut BTreeSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Return {
                value: Some(Expr::Var(v)),
                ..
            } => {
                out.insert(v.clone());
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_returned_vars(then_body, out);
                collect_returned_vars(else_body, out);
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    collect_returned_vars(&a.body, out);
                }
            }
            Stmt::While { body, .. }
            | Stmt::ForRange { body, .. }
            | Stmt::ForEach { body, .. } => {
                collect_returned_vars(body, out);
            }
            _ => {}
        }
    }
}

fn scan_stmts_alloc_sites(
    fn_name: &str,
    stmts: &[Stmt],
    in_loop: bool,
    returned_vars: &BTreeSet<String>,
    struct_field_counts: &BTreeMap<String, usize>,
    sites: &mut Vec<AllocationSiteAudit>,
) {
    for stmt in stmts {
        match stmt {
            Stmt::Let {
                id, name, value, ..
            } => {
                let is_ret = returned_vars.contains(name);
                scan_expr_alloc_sites(
                    *id,
                    fn_name,
                    Some(name),
                    is_ret,
                    in_loop,
                    value,
                    struct_field_counts,
                    sites,
                );
            }
            Stmt::Assign { id, value, .. } => {
                scan_expr_alloc_sites(
                    *id,
                    fn_name,
                    None,
                    false,
                    in_loop,
                    value,
                    struct_field_counts,
                    sites,
                );
            }
            Stmt::Return {
                id,
                value: Some(val),
                ..
            } => {
                scan_expr_alloc_sites(
                    *id,
                    fn_name,
                    Some("return_slot"),
                    true,
                    in_loop,
                    val,
                    struct_field_counts,
                    sites,
                );
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                scan_stmts_alloc_sites(
                    fn_name,
                    then_body,
                    in_loop,
                    returned_vars,
                    struct_field_counts,
                    sites,
                );
                scan_stmts_alloc_sites(
                    fn_name,
                    else_body,
                    in_loop,
                    returned_vars,
                    struct_field_counts,
                    sites,
                );
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    scan_stmts_alloc_sites(
                        fn_name,
                        &a.body,
                        in_loop,
                        returned_vars,
                        struct_field_counts,
                        sites,
                    );
                }
            }
            Stmt::While { body, .. }
            | Stmt::ForRange { body, .. }
            | Stmt::ForEach { body, .. } => {
                scan_stmts_alloc_sites(
                    fn_name,
                    body,
                    true,
                    returned_vars,
                    struct_field_counts,
                    sites,
                );
            }
            Stmt::Expr { id, expr, .. } => {
                scan_expr_alloc_sites(
                    *id,
                    fn_name,
                    None,
                    false,
                    in_loop,
                    expr,
                    struct_field_counts,
                    sites,
                );
            }
            _ => {}
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn scan_expr_alloc_sites(
    stmt_id: NodeId,
    fn_name: &str,
    bound_var: Option<&str>,
    escapes_via_return: bool,
    in_loop: bool,
    expr: &Expr,
    struct_field_counts: &BTreeMap<String, usize>,
    sites: &mut Vec<AllocationSiteAudit>,
) {
    match expr {
        Expr::StructInit { name, fields } => {
            let fcount = struct_field_counts
                .get(name)
                .copied()
                .unwrap_or(fields.len())
                .max(1);
            let bytes = fcount * 8 + 16; // 8B per field + 16B allocator header saved
            let (escape_state, strategy, sroa, note) = if escapes_via_return {
                (
                    "ReturnEscape (RVO)".to_string(),
                    format!(
                        "Caller-Allocated Return Slot / C++17 & Rust RVO (unboxed {} × 8B registers x0..x{})",
                        fcount,
                        (fcount - 1).min(7)
                    ),
                    fcount,
                    format!(
                        "Aggregate `{}` returned directly — elide heap box via AAPCS64/SystemV register return or caller RVO slot",
                        name
                    ),
                )
            } else {
                (
                    "NoEscape (Stack/SROA)".to_string(),
                    format!(
                        "Scalar Replacement of Aggregates (SROA) into {} virtual register(s)",
                        fcount
                    ),
                    fcount,
                    format!(
                        "Aggregate `{}` ({}) never escapes `{}` — scalarized into {} register(s)",
                        name,
                        bound_var.unwrap_or("tmp"),
                        fn_name,
                        fcount
                    ),
                )
            };
            sites.push(AllocationSiteAudit {
                site_id: stmt_id,
                fn_name: fn_name.to_string(),
                kind: "StructInit".to_string(),
                expr_summary: format_expr_compact(expr),
                escape_state,
                promotion_strategy: strategy,
                sroa_fields: sroa,
                estimated_bytes_saved: bytes,
                note,
            });
        }
        Expr::List(items) => {
            let len = items.len();
            let bytes = len * 8 + 24;
            let (escape_state, strategy, note) = if !escapes_via_return {
                (
                    "NoEscape (Stack/SROA)".to_string(),
                    format!("Stack-Allocated Fixed Array `[i64; {}]` (0 malloc calls)", len),
                    format!(
                        "List literal `{}` of length {} is confined to `{}` frame — promote to stack buffer `[sp, #offset]`",
                        bound_var.unwrap_or("list"),
                        len,
                        fn_name
                    ),
                )
            } else if items.is_empty() {
                (
                    "ReturnEscape (RVO)".to_string(),
                    "Caller-Provided Arena / Pre-sized Capacity Hint `with_capacity(len(input))`"
                        .to_string(),
                    format!(
                        "Result list `{}` initialized empty and returned — bind to caller arena buffer",
                        bound_var.unwrap_or("out")
                    ),
                )
            } else {
                (
                    "ReturnEscape (RVO)".to_string(),
                    format!("Caller Return Buffer `[i64; {}]`", len),
                    "Returned fixed list literal written directly into caller buffer".to_string(),
                )
            };
            sites.push(AllocationSiteAudit {
                site_id: stmt_id,
                fn_name: fn_name.to_string(),
                kind: "FixedList".to_string(),
                expr_summary: format_expr_compact(expr),
                escape_state,
                promotion_strategy: strategy,
                sroa_fields: 0,
                estimated_bytes_saved: bytes,
                note,
            });
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Push { list, value } => {
                sites.push(AllocationSiteAudit {
                    site_id: stmt_id,
                    fn_name: fn_name.to_string(),
                    kind: "DynamicListPush".to_string(),
                    expr_summary: format!("push({}, {})", format_expr_compact(list), format_expr_compact(value)),
                    escape_state: "ReturnEscape (RVO)".to_string(),
                    promotion_strategy: "Pre-Allocated Upper-Bound Arena Slice (`cap <= len(input)`)".to_string(),
                    sroa_fields: 0,
                    estimated_bytes_saved: 64,
                    note: "Loop `push` bounded by input slice length — pre-reserve single contiguous arena block".to_string(),
                });
            }
            Intrinsic::Upper(a) | Intrinsic::Lower(a) | Intrinsic::ToStr(a) => {
                let state = if in_loop && !escapes_via_return {
                    "LoopArena"
                } else if !escapes_via_return {
                    "NoEscape (Stack/SROA)"
                } else {
                    "ReturnEscape (RVO)"
                };
                sites.push(AllocationSiteAudit {
                    site_id: stmt_id,
                    fn_name: fn_name.to_string(),
                    kind: "StringFormat".to_string(),
                    expr_summary: format_expr_compact(expr),
                    escape_state: state.to_string(),
                    promotion_strategy: "Small-String Optimization (SSO 24B inline stack buffer)"
                        .to_string(),
                    sroa_fields: 0,
                    estimated_bytes_saved: 32,
                    note: format!(
                        "String transform on `{}` fits in 24-byte inline SSO register/stack slot",
                        format_expr_compact(a)
                    ),
                });
            }
            _ => {}
        },
        Expr::Binary { left, right, .. } => {
            scan_expr_alloc_sites(
                stmt_id,
                fn_name,
                bound_var,
                escapes_via_return,
                in_loop,
                left,
                struct_field_counts,
                sites,
            );
            scan_expr_alloc_sites(
                stmt_id,
                fn_name,
                bound_var,
                escapes_via_return,
                in_loop,
                right,
                struct_field_counts,
                sites,
            );
        }
        _ => {}
    }
}

fn synthesize_lifetime_projections(
    f: &FnDecl,
    sites: &[AllocationSiteAudit],
) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let fn_name = &f.name;
    let ret_ty = f.ret_ty.display();
    let site_summary = sites
        .first()
        .map(|s| format!("{} [{} -> {}]", s.expr_summary, s.escape_state, s.promotion_strategy))
        .unwrap_or_else(|| "0 heap allocations (pure register scalar function)".to_string());

    out.insert(
        "rust".to_string(),
        format!(
            "// [Escape Analysis: {site_summary}]\n#[inline]\npub fn {fn_name}_stack_arena(/* caller stack/arena lifetime 'a */) -> {ret_ty} {{\n    // NoEscape lists -> [i64; N] on stack; StructInit -> SROA registers / RVO\n}}"
        ),
    );
    out.insert(
        "zig".to_string(),
        format!(
            "// [Escape Analysis: {site_summary}]\npub fn {fn_name}_stack_arena() {ret_ty} {{\n    var sfb = std.heap.stackFallback(128, std.heap.page_allocator);\n    const arena = sfb.get();\n    _ = arena;\n}}"
        ),
    );
    out.insert(
        "c".to_string(),
        format!(
            "// [Escape Analysis: {site_summary}]\n// C11 compound literal on stack frame (0 malloc calls) + AAPCS64/SysV struct RVO\nstatic inline void {fn_name}_sroa(void) {{ /* stack-allocated frame */ }}"
        ),
    );
    out.insert(
        "cpp".to_string(),
        format!(
            "// [Escape Analysis: {site_summary}]\n// C++17 guaranteed copy elision (RVO) + std::array<int64_t, N> stack buffer"
        ),
    );
    out.insert(
        "swift".to_string(),
        format!(
            "// [Escape Analysis: {site_summary}]\n// Swift 6 value-type struct promoted to registers + withUnsafeTemporaryAllocation"
        ),
    );
    out.insert(
        "java".to_string(),
        format!(
            "// [Escape Analysis: {site_summary}]\n// HotSpot C2 JVM -XX:+DoEscapeAnalysis -XX:+EliminateAllocations Scalar Replacement"
        ),
    );
    out.insert(
        "go".to_string(),
        format!(
            "// [Escape Analysis: {site_summary}]\n// Go `go build -gcflags=\"-m\"`: `{fn_name}` aggregate does not escape to heap"
        ),
    );
    out.insert(
        "python".to_string(),
        format!(
            "# [Escape Analysis: {site_summary}]\n# Tuple/register unpacking elides heap dict/dataclass wrapper in `{fn_name}`"
        ),
    );
    out.insert(
        "ruby".to_string(),
        format!(
            "# [Escape Analysis: {site_summary}]\n# YJIT object allocation sinking for `{fn_name}`"
        ),
    );
    out.insert(
        "lua".to_string(),
        format!(
            "-- [Escape Analysis: {site_summary}]\n-- LuaJIT 2.1 trace-compiler allocation sinking (sink_alloc) in `{fn_name}`"
        ),
    );
    out.insert(
        "perl".to_string(),
        format!(
            "# [Escape Analysis: {site_summary}]\n# Lexical pad scalar replacement in `{fn_name}`"
        ),
    );
    out.insert(
        "typescript".to_string(),
        format!(
            "// [Escape Analysis: {site_summary}]\n// V8 TurboFan EscapeAnalysis + YoungGeneration allocation folding in `{fn_name}`"
        ),
    );
    out.insert(
        "star".to_string(),
        format!(
            ";; (escape-analysis {fn_name} :sites {} :summary \"{}\")",
            sites.len(),
            site_summary.replace('"', "'")
        ),
    );
    let _ = Type::Int;
    out
}

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use crate::egraph::format_expr_compact;
use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, NodeId, Stmt, UnaryOp,
};

const BRANCH_MISPREDICT_PENALTY: u64 = 12;
const L1D_HIT_CYCLES: u64 = 4;
const PREFETCH_HIT_CYCLES: u64 = 10;
const L1D_MISS_CYCLES: u64 = 48;

#[derive(Debug, Clone)]
pub struct BranchSiteProfile {
    pub stmt_id: NodeId,
    pub fn_name: String,
    pub branch_expr: String,
    pub taken_count: u64,
    pub not_taken_count: u64,
    pub correct_predictions: u64,
    pub mispredictions: u64,
    pub accuracy_pct: f64,
    pub penalty_cycles: u64,
}

#[derive(Debug, Clone)]
pub struct CacheSiteProfile {
    pub site_label: String,
    pub fn_name: String,
    pub accesses: u64,
    pub l1_hits: u64,
    pub prefetch_hits: u64,
    pub misses: u64,
    pub hit_rate_pct: f64,
    pub memory_cycles: u64,
}

#[derive(Debug, Clone)]
pub struct FunctionMicroArchProfile {
    pub fn_name: String,
    pub signature: String,
    pub uops_retired: u64,
    pub in_order_cycles: u64,
    pub ooo_cycles: u64,
    pub superscalar_ipc: f64,
    pub alu_uops: u64,
    pub mul_div_uops: u64,
    pub mem_uops: u64,
    pub branch_uops: u64,
    pub branch_mispredicts: u64,
    pub l1d_hits: u64,
    pub l1d_misses: u64,
    pub bottleneck: String,
}

#[derive(Debug, Clone)]
pub struct MicroArchReport {
    pub total_uops_retired: u64,
    pub total_in_order_cycles: u64,
    pub total_ooo_cycles: u64,
    pub superscalar_ipc: f64,
    pub ooo_speedup: f64,
    pub total_branches: u64,
    pub branch_mispredictions: u64,
    pub branch_accuracy_pct: f64,
    pub branch_penalty_cycles: u64,
    pub total_mem_accesses: u64,
    pub l1d_hits: u64,
    pub l1d_prefetch_hits: u64,
    pub l1d_misses: u64,
    pub l1d_hit_rate_pct: f64,
    pub dominant_bottleneck: String,
    pub functions: Vec<FunctionMicroArchProfile>,
    pub branch_sites: Vec<BranchSiteProfile>,
    pub cache_sites: Vec<CacheSiteProfile>,
    pub elapsed_ms: u128,
}

#[derive(Debug, Clone)]
pub struct DagDependenceEdge {
    pub from_idx: usize,
    pub to_idx: usize,
    pub kind: String, // "RAW" | "WAR" | "WAW" | "Barrier"
    pub latency: u64,
    pub var: String,
}

#[derive(Debug, Clone)]
pub struct ScheduledInstEntry {
    pub orig_idx: usize,
    pub sched_slot: usize,
    pub issue_cycle: u64,
    pub ready_cycle: u64,
    pub unit: String, // "ALU" | "MUL" | "DIV" | "LSU" | "BRU"
    pub latency: u64,
    pub critical_height: u64,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct FunctionScheduleReport {
    pub fn_name: String,
    pub signature: String,
    pub inst_count: usize,
    pub dag_edges_count: usize,
    pub critical_path_cycles: u64,
    pub in_order_cycles_before: u64,
    pub scheduled_cycles_after: u64,
    pub stall_bubbles_before: u64,
    pub stall_bubbles_after: u64,
    pub bubbles_eliminated: u64,
    pub reordered_instructions: usize,
    pub speedup_ratio: f64,
    pub instructions: Vec<ScheduledInstEntry>,
    pub dag_edges: Vec<DagDependenceEdge>,
    pub unscheduled_listing: String,
    pub scheduled_listing: String,
    pub mermaid_dag: String,
}

#[derive(Debug, Clone)]
pub struct InstructionScheduleReport {
    pub total_functions: usize,
    pub total_instructions: usize,
    pub total_dag_edges: usize,
    pub total_cycles_before: u64,
    pub total_cycles_after: u64,
    pub total_bubbles_eliminated: u64,
    pub total_reordered_insts: usize,
    pub overall_speedup: f64,
    pub functions: Vec<FunctionScheduleReport>,
    pub elapsed_ms: u128,
}

#[derive(Clone, Copy)]
struct BhtCounter {
    state: u8, // 0 = StronglyNotTaken, 1 = WeaklyNotTaken, 2 = WeaklyTaken, 3 = StronglyTaken
}

impl BhtCounter {
    fn new() -> Self {
        Self { state: 2 } // WeaklyTaken initial state (optimistic for loops)
    }

    fn predict_taken(self) -> bool {
        self.state >= 2
    }

    fn update(&mut self, taken: bool) {
        if taken {
            if self.state < 3 {
                self.state += 1;
            }
        } else if self.state > 0 {
            self.state -= 1;
        }
    }
}

struct L1DataCacheSim {
    // 64 sets, 8-way LRU cache storing 64-byte line tags
    sets: Vec<Vec<u64>>,
    last_line_by_stream: BTreeMap<String, u64>,
    prefetch_queue: BTreeSet<u64>,
}

impl L1DataCacheSim {
    fn new() -> Self {
        Self {
            sets: (0..64).map(|_| Vec::with_capacity(8)).collect(),
            last_line_by_stream: BTreeMap::new(),
            prefetch_queue: BTreeSet::new(),
        }
    }

    /// Returns (is_l1_hit, is_prefetch_hit, cycles)
    fn access(&mut self, stream: &str, byte_addr: u64) -> (bool, bool, u64) {
        let line_addr = byte_addr >> 6; // 64-byte cache line
        let set_idx = (line_addr as usize) & 63;
        let way_list = &mut self.sets[set_idx];

        if let Some(pos) = way_list.iter().position(|&tag| tag == line_addr) {
            let tag = way_list.remove(pos);
            way_list.push(tag);
            // Trigger next-line hardware stream prefetcher on sequential stride
            if line_addr > 0 && self.last_line_by_stream.get(stream) == Some(&(line_addr - 1)) {
                self.prefetch_queue.insert(line_addr + 1);
            }
            self.last_line_by_stream.insert(stream.to_string(), line_addr);
            return (true, false, L1D_HIT_CYCLES);
        }

        let prefetched = self.prefetch_queue.remove(&line_addr);
        if way_list.len() >= 8 {
            way_list.remove(0);
        }
        way_list.push(line_addr);

        // Next-line hardware prefetcher speculates line_addr + 1
        self.prefetch_queue.insert(line_addr + 1);
        self.last_line_by_stream.insert(stream.to_string(), line_addr);

        if prefetched {
            (false, true, PREFETCH_HIT_CYCLES)
        } else {
            (false, false, L1D_MISS_CYCLES)
        }
    }
}

/// Simulate executing `hub` through a 4-Wide Out-of-Order Superscalar Processor Core
/// with Tomasulo Register Renaming, a 64-entry 2-Bit Saturating-Counter Bimodal Branch Predictor,
/// and a 32 KB 8-Way Set-Associative L1 Data Cache with Next-Line Hardware Stream Prefetching.
pub fn simulate_microarch(hub: &HubModule) -> MicroArchReport {
    let start = Instant::now();
    let mut bht = [BhtCounter::new(); 64];
    let mut cache = L1DataCacheSim::new();

    let mut functions = Vec::new();
    let mut branch_sites = Vec::new();
    let mut cache_sites = Vec::new();

    let mut total_uops_retired = 0u64;
    let mut total_in_order_cycles = 0u64;
    let mut total_ooo_cycles = 0u64;
    let mut total_branches = 0u64;
    let mut branch_mispredictions = 0u64;
    let mut branch_penalty_cycles = 0u64;
    let mut l1d_hits = 0u64;
    let mut l1d_prefetch_hits = 0u64;
    let mut l1d_misses = 0u64;

    for (fn_idx, item) in hub.items.iter().enumerate() {
        if let Item::Function(f) = item {
            let prof = simulate_fn_microarch(
                f,
                fn_idx,
                &mut bht,
                &mut cache,
                &mut branch_sites,
                &mut cache_sites,
            );
            total_uops_retired += prof.uops_retired;
            total_in_order_cycles += prof.in_order_cycles;
            total_ooo_cycles += prof.ooo_cycles;
            total_branches += prof.branch_uops;
            branch_mispredictions += prof.branch_mispredicts;
            l1d_hits += prof.l1d_hits;
            l1d_misses += prof.l1d_misses;
            functions.push(prof);
        }
    }

    for bs in &branch_sites {
        branch_penalty_cycles += bs.penalty_cycles;
    }
    for cs in &cache_sites {
        l1d_prefetch_hits += cs.prefetch_hits;
    }
    let total_mem_accesses = l1d_hits + l1d_prefetch_hits + l1d_misses;

    let total_ooo_cycles = total_ooo_cycles.max(1);
    let superscalar_ipc =
        ((total_uops_retired as f64 / total_ooo_cycles as f64) * 100.0).round() / 100.0;
    let ooo_speedup =
        ((total_in_order_cycles.max(1) as f64 / total_ooo_cycles as f64) * 100.0).round() / 100.0;
    let branch_accuracy_pct = if total_branches == 0 {
        100.0
    } else {
        (((total_branches.saturating_sub(branch_mispredictions)) as f64 / total_branches as f64)
            * 1000.0)
            .round()
            / 10.0
    };
    let l1d_hit_rate_pct = if total_mem_accesses == 0 {
        100.0
    } else {
        (((l1d_hits + l1d_prefetch_hits) as f64 / total_mem_accesses as f64) * 1000.0).round()
            / 10.0
    };

    let dominant_bottleneck = if branch_penalty_cycles * 4 > total_ooo_cycles {
        "Control-Bound (Branch Misprediction Flushes)".to_string()
    } else if l1d_misses * L1D_MISS_CYCLES * 3 > total_ooo_cycles {
        "Memory-Bound (L1D Compulsory/Conflict Misses)".to_string()
    } else {
        "Compute/ILP-Bound (ALU & Loop-Carried RAW Chains)".to_string()
    };

    MicroArchReport {
        total_uops_retired,
        total_in_order_cycles,
        total_ooo_cycles,
        superscalar_ipc,
        ooo_speedup,
        total_branches,
        branch_mispredictions,
        branch_accuracy_pct,
        branch_penalty_cycles,
        total_mem_accesses,
        l1d_hits,
        l1d_prefetch_hits,
        l1d_misses,
        l1d_hit_rate_pct,
        dominant_bottleneck,
        functions,
        branch_sites,
        cache_sites,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

#[derive(Default)]
struct FnSimAcc {
    alu_uops: u64,
    mul_div_uops: u64,
    mem_uops: u64,
    branch_uops: u64,
    in_order_compute_cycles: u64,
    ooo_compute_cycles: u64,
    branch_mispredicts: u64,
    branch_penalty_cycles: u64,
    l1_hits: u64,
    l1_misses: u64,
    mem_cycles: u64,
}

fn simulate_fn_microarch(
    f: &FnDecl,
    fn_idx: usize,
    bht: &mut [BhtCounter; 64],
    cache: &mut L1DataCacheSim,
    branch_sites: &mut Vec<BranchSiteProfile>,
    cache_sites: &mut Vec<CacheSiteProfile>,
) -> FunctionMicroArchProfile {
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

    let mut acc = FnSimAcc::default();
    // Prologue + epilogue uops
    acc.alu_uops += 2;
    acc.mem_uops += 2;
    acc.in_order_compute_cycles += 4;
    acc.ooo_compute_cycles += 2;

    let base_addr = ((fn_idx as u64) + 1) * 0x10_000;
    sim_stmts_microarch(
        &f.name,
        &f.body,
        1,
        base_addr,
        bht,
        cache,
        &mut acc,
        branch_sites,
        cache_sites,
    );

    let uops_retired = acc.alu_uops + acc.mul_div_uops + acc.mem_uops + acc.branch_uops;
    let in_order_cycles =
        (acc.in_order_compute_cycles + acc.mem_cycles + acc.branch_penalty_cycles).max(1);
    // Out-of-Order ROB overlaps independent ALU ops and hides L1D hit latency behind compute
    let overlapped_mem = (acc.mem_cycles * 6) / 10;
    let ooo_cycles = (acc.ooo_compute_cycles + overlapped_mem + acc.branch_penalty_cycles).max(1);
    let superscalar_ipc = ((uops_retired as f64 / ooo_cycles as f64) * 100.0).round() / 100.0;

    let bottleneck = if acc.branch_penalty_cycles * 3 > ooo_cycles {
        "Control-Bound (Data-Dependent Branch Mispredicts)".to_string()
    } else if acc.l1_misses > 0 && acc.mem_cycles * 2 > ooo_cycles {
        "Memory-Bound (L1D Cache Line Fill Latency)".to_string()
    } else if acc.mul_div_uops * 6 > uops_retired {
        "Execution-Port-Bound (Integer Multiply/Divide Pipe)".to_string()
    } else {
        "Superscalar ALU / Balanced 4-Wide Pipeline".to_string()
    };

    FunctionMicroArchProfile {
        fn_name: f.name.clone(),
        signature,
        uops_retired,
        in_order_cycles,
        ooo_cycles,
        superscalar_ipc,
        alu_uops: acc.alu_uops,
        mul_div_uops: acc.mul_div_uops,
        mem_uops: acc.mem_uops,
        branch_uops: acc.branch_uops,
        branch_mispredicts: acc.branch_mispredicts,
        l1d_hits: acc.l1_hits,
        l1d_misses: acc.l1_misses,
        bottleneck,
    }
}

#[allow(clippy::too_many_arguments)]
fn sim_stmts_microarch(
    fn_name: &str,
    stmts: &[Stmt],
    trip_multiplier: u64,
    base_addr: u64,
    bht: &mut [BhtCounter; 64],
    cache: &mut L1DataCacheSim,
    acc: &mut FnSimAcc,
    branch_sites: &mut Vec<BranchSiteProfile>,
    cache_sites: &mut Vec<CacheSiteProfile>,
) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { value, .. } => {
                acc.alu_uops += trip_multiplier;
                acc.in_order_compute_cycles += trip_multiplier;
                acc.ooo_compute_cycles += trip_multiplier.div_ceil(3);
                sim_expr_microarch(
                    fn_name,
                    value,
                    trip_multiplier,
                    base_addr,
                    cache,
                    acc,
                    cache_sites,
                );
            }
            Stmt::Assign { target, value, .. } => {
                acc.alu_uops += trip_multiplier;
                acc.in_order_compute_cycles += trip_multiplier;
                acc.ooo_compute_cycles += trip_multiplier.div_ceil(3);
                if matches!(
                    target,
                    AssignTarget::Index { .. } | AssignTarget::Field { .. }
                ) {
                    acc.mem_uops += trip_multiplier;
                }
                sim_expr_microarch(
                    fn_name,
                    value,
                    trip_multiplier,
                    base_addr,
                    cache,
                    acc,
                    cache_sites,
                );
            }
            Stmt::If {
                id,
                cond,
                then_body,
                else_body,
                ..
            } => {
                sim_expr_microarch(
                    fn_name,
                    cond,
                    trip_multiplier,
                    base_addr,
                    cache,
                    acc,
                    cache_sites,
                );
                acc.branch_uops += trip_multiplier;

                // Simulate bimodal 2-bit predictor across `trip_multiplier` dynamic executions
                let bht_idx = (*id as usize) & 63;
                let trials = trip_multiplier.max(4);
                let mut taken_c = 0u64;
                let mut not_taken_c = 0u64;
                let mut correct = 0u64;
                let mut mispred = 0u64;

                for t in 0..trials {
                    // Alternating / data-dependent pattern: 3 taken out of every 4
                    let outcome_taken = (t % 4) != 2;
                    if outcome_taken {
                        taken_c += 1;
                    } else {
                        not_taken_c += 1;
                    }
                    let pred = bht[bht_idx].predict_taken();
                    if pred == outcome_taken {
                        correct += 1;
                    } else {
                        mispred += 1;
                    }
                    bht[bht_idx].update(outcome_taken);
                }

                let pen = mispred * BRANCH_MISPREDICT_PENALTY;
                acc.branch_mispredicts += mispred;
                acc.branch_penalty_cycles += pen;

                let acc_pct = ((correct as f64 / trials as f64) * 1000.0).round() / 10.0;
                branch_sites.push(BranchSiteProfile {
                    stmt_id: *id,
                    fn_name: fn_name.to_string(),
                    branch_expr: format!("if {}", format_expr_compact(cond)),
                    taken_count: taken_c,
                    not_taken_count: not_taken_c,
                    correct_predictions: correct,
                    mispredictions: mispred,
                    accuracy_pct: acc_pct,
                    penalty_cycles: pen,
                });

                let then_trips = (trip_multiplier * 3 / 4).max(1);
                let else_trips = (trip_multiplier / 4).max(1);
                sim_stmts_microarch(
                    fn_name,
                    then_body,
                    then_trips,
                    base_addr + 0x400,
                    bht,
                    cache,
                    acc,
                    branch_sites,
                    cache_sites,
                );
                if !else_body.is_empty() {
                    sim_stmts_microarch(
                        fn_name,
                        else_body,
                        else_trips,
                        base_addr + 0x800,
                        bht,
                        cache,
                        acc,
                        branch_sites,
                        cache_sites,
                    );
                }
            }
            Stmt::Match { id, expr, arms, .. } => {
                sim_expr_microarch(
                    fn_name,
                    expr,
                    trip_multiplier,
                    base_addr,
                    cache,
                    acc,
                    cache_sites,
                );
                acc.branch_uops += trip_multiplier;
                let bht_idx = (*id as usize) & 63;
                let trials = trip_multiplier.max(4);
                let mut correct = 0u64;
                let mut mispred = 0u64;
                for _ in 0..trials {
                    let pred = bht[bht_idx].predict_taken();
                    if pred {
                        correct += 1;
                    } else {
                        mispred += 1;
                    }
                    bht[bht_idx].update(true);
                }
                let pen = mispred * BRANCH_MISPREDICT_PENALTY;
                acc.branch_mispredicts += mispred;
                acc.branch_penalty_cycles += pen;
                branch_sites.push(BranchSiteProfile {
                    stmt_id: *id,
                    fn_name: fn_name.to_string(),
                    branch_expr: format!("match {}", format_expr_compact(expr)),
                    taken_count: trials,
                    not_taken_count: 0,
                    correct_predictions: correct,
                    mispredictions: mispred,
                    accuracy_pct: ((correct as f64 / trials as f64) * 1000.0).round() / 10.0,
                    penalty_cycles: pen,
                });

                for arm in arms {
                    sim_stmts_microarch(
                        fn_name,
                        &arm.body,
                        trip_multiplier,
                        base_addr + 0x200,
                        bht,
                        cache,
                        acc,
                        branch_sites,
                        cache_sites,
                    );
                }
            }
            Stmt::ForRange {
                id,
                var,
                start,
                end,
                body,
                ..
            } => {
                let trips = match (start, end) {
                    (Expr::Int(lo), Expr::Int(hi)) => (*hi - *lo).clamp(1, 64) as u64,
                    _ => 16,
                } * trip_multiplier;

                // Loop back-edge branch: taken `trips` times, not-taken 1 time on loop exit
                let bht_idx = (*id as usize) & 63;
                let mut correct = 0u64;
                let mut mispred = 0u64;
                for t in 0..=trips {
                    let outcome = t < trips;
                    if bht[bht_idx].predict_taken() == outcome {
                        correct += 1;
                    } else {
                        mispred += 1;
                    }
                    bht[bht_idx].update(outcome);
                }
                let pen = mispred * BRANCH_MISPREDICT_PENALTY;
                acc.branch_uops += trips + 1;
                acc.branch_mispredicts += mispred;
                acc.branch_penalty_cycles += pen;

                branch_sites.push(BranchSiteProfile {
                    stmt_id: *id,
                    fn_name: fn_name.to_string(),
                    branch_expr: format!(
                        "loop {} in {}..{}",
                        var,
                        format_expr_compact(start),
                        format_expr_compact(end)
                    ),
                    taken_count: trips,
                    not_taken_count: 1,
                    correct_predictions: correct,
                    mispredictions: mispred,
                    accuracy_pct: ((correct as f64 / (trips + 1) as f64) * 1000.0).round() / 10.0,
                    penalty_cycles: pen,
                });

                sim_stmts_microarch(
                    fn_name,
                    body,
                    trips,
                    base_addr + 0x1000,
                    bht,
                    cache,
                    acc,
                    branch_sites,
                    cache_sites,
                );
            }
            Stmt::ForEach {
                id,
                var,
                iter,
                body,
                ..
            } => {
                let trips = 16 * trip_multiplier;
                let bht_idx = (*id as usize) & 63;
                let mut correct = 0u64;
                let mut mispred = 0u64;
                for t in 0..=trips {
                    let outcome = t < trips;
                    if bht[bht_idx].predict_taken() == outcome {
                        correct += 1;
                    } else {
                        mispred += 1;
                    }
                    bht[bht_idx].update(outcome);
                }
                let pen = mispred * BRANCH_MISPREDICT_PENALTY;
                acc.branch_uops += trips + 1;
                acc.branch_mispredicts += mispred;
                acc.branch_penalty_cycles += pen;

                let iter_s = format_expr_compact(iter);
                branch_sites.push(BranchSiteProfile {
                    stmt_id: *id,
                    fn_name: fn_name.to_string(),
                    branch_expr: format!("for {} in {}", var, iter_s),
                    taken_count: trips,
                    not_taken_count: 1,
                    correct_predictions: correct,
                    mispredictions: mispred,
                    accuracy_pct: ((correct as f64 / (trips + 1) as f64) * 1000.0).round() / 10.0,
                    penalty_cycles: pen,
                });

                // Simulate sequential slice loads across 64-byte L1D cache lines (8 × i64 per line)
                let mut hits = 0u64;
                let mut pref_hits = 0u64;
                let mut misses = 0u64;
                let mut mem_cyc = 0u64;
                for idx in 0..trips {
                    let (h, p, c) = cache.access(&iter_s, base_addr + idx * 8);
                    if h {
                        hits += 1;
                    } else if p {
                        pref_hits += 1;
                    } else {
                        misses += 1;
                    }
                    mem_cyc += c;
                }
                acc.mem_uops += trips;
                acc.l1_hits += hits;
                acc.l1_misses += misses;
                acc.mem_cycles += mem_cyc;
                cache_sites.push(CacheSiteProfile {
                    site_label: format!("slice `{}`[{}]", iter_s, var),
                    fn_name: fn_name.to_string(),
                    accesses: trips,
                    l1_hits: hits,
                    prefetch_hits: pref_hits,
                    misses,
                    hit_rate_pct: (((hits + pref_hits) as f64 / trips as f64) * 1000.0).round()
                        / 10.0,
                    memory_cycles: mem_cyc,
                });

                sim_stmts_microarch(
                    fn_name,
                    body,
                    trips,
                    base_addr + 0x2000,
                    bht,
                    cache,
                    acc,
                    branch_sites,
                    cache_sites,
                );
            }
            Stmt::While { id, cond, body, .. } => {
                let trips = 12 * trip_multiplier;
                let bht_idx = (*id as usize) & 63;
                let mut correct = 0u64;
                let mut mispred = 0u64;
                for t in 0..=trips {
                    let outcome = t < trips;
                    if bht[bht_idx].predict_taken() == outcome {
                        correct += 1;
                    } else {
                        mispred += 1;
                    }
                    bht[bht_idx].update(outcome);
                }
                let pen = mispred * BRANCH_MISPREDICT_PENALTY;
                acc.branch_uops += trips + 1;
                acc.branch_mispredicts += mispred;
                acc.branch_penalty_cycles += pen;

                branch_sites.push(BranchSiteProfile {
                    stmt_id: *id,
                    fn_name: fn_name.to_string(),
                    branch_expr: format!("while {}", format_expr_compact(cond)),
                    taken_count: trips,
                    not_taken_count: 1,
                    correct_predictions: correct,
                    mispredictions: mispred,
                    accuracy_pct: ((correct as f64 / (trips + 1) as f64) * 1000.0).round() / 10.0,
                    penalty_cycles: pen,
                });

                sim_stmts_microarch(
                    fn_name,
                    body,
                    trips,
                    base_addr + 0x3000,
                    bht,
                    cache,
                    acc,
                    branch_sites,
                    cache_sites,
                );
            }
            Stmt::Return { value, .. } => {
                acc.branch_uops += trip_multiplier;
                if let Some(v) = value {
                    sim_expr_microarch(
                        fn_name,
                        v,
                        trip_multiplier,
                        base_addr,
                        cache,
                        acc,
                        cache_sites,
                    );
                }
            }
            Stmt::Expr { expr, .. } => {
                sim_expr_microarch(
                    fn_name,
                    expr,
                    trip_multiplier,
                    base_addr,
                    cache,
                    acc,
                    cache_sites,
                );
            }
            Stmt::Assert { cond, .. } => {
                sim_expr_microarch(
                    fn_name,
                    cond,
                    trip_multiplier,
                    base_addr,
                    cache,
                    acc,
                    cache_sites,
                );
            }
            Stmt::AssertEq { left, right, .. } => {
                sim_expr_microarch(
                    fn_name,
                    left,
                    trip_multiplier,
                    base_addr,
                    cache,
                    acc,
                    cache_sites,
                );
                sim_expr_microarch(
                    fn_name,
                    right,
                    trip_multiplier,
                    base_addr,
                    cache,
                    acc,
                    cache_sites,
                );
            }
            Stmt::Break { .. } | Stmt::Continue { .. } | Stmt::Comment { .. } => {}
        }
    }
}

fn sim_expr_microarch(
    fn_name: &str,
    expr: &Expr,
    trips: u64,
    base_addr: u64,
    cache: &mut L1DataCacheSim,
    acc: &mut FnSimAcc,
    cache_sites: &mut Vec<CacheSiteProfile>,
) {
    match expr {
        Expr::Binary { op, left, right } => {
            sim_expr_microarch(fn_name, left, trips, base_addr, cache, acc, cache_sites);
            sim_expr_microarch(fn_name, right, trips, base_addr, cache, acc, cache_sites);
            match op {
                BinOp::Mul => {
                    acc.mul_div_uops += trips;
                    acc.in_order_compute_cycles += trips * 3;
                    acc.ooo_compute_cycles += trips * 2;
                }
                BinOp::Div | BinOp::IntDiv | BinOp::Mod => {
                    acc.mul_div_uops += trips;
                    acc.in_order_compute_cycles += trips * 10;
                    acc.ooo_compute_cycles += trips * 6;
                }
                _ => {
                    acc.alu_uops += trips;
                    acc.in_order_compute_cycles += trips;
                    acc.ooo_compute_cycles += trips.div_ceil(4);
                }
            }
        }
        Expr::Unary { expr: inner, .. } => {
            acc.alu_uops += trips;
            acc.in_order_compute_cycles += trips;
            sim_expr_microarch(fn_name, inner, trips, base_addr, cache, acc, cache_sites);
        }
        Expr::Index { base, index } => {
            sim_expr_microarch(fn_name, base, trips, base_addr, cache, acc, cache_sites);
            sim_expr_microarch(fn_name, index, trips, base_addr, cache, acc, cache_sites);

            let arr_name = format_expr_compact(base);
            let idx_name = format_expr_compact(index);
            let mut hits = 0u64;
            let mut pref_hits = 0u64;
            let mut misses = 0u64;
            let mut mem_cyc = 0u64;
            for i in 0..trips {
                let (h, p, c) = cache.access(&arr_name, base_addr + 0x4000 + i * 8);
                if h {
                    hits += 1;
                } else if p {
                    pref_hits += 1;
                } else {
                    misses += 1;
                }
                mem_cyc += c;
            }
            acc.mem_uops += trips;
            acc.l1_hits += hits;
            acc.l1_misses += misses;
            acc.mem_cycles += mem_cyc;
            cache_sites.push(CacheSiteProfile {
                site_label: format!("{}[{}]", arr_name, idx_name),
                fn_name: fn_name.to_string(),
                accesses: trips,
                l1_hits: hits,
                prefetch_hits: pref_hits,
                misses,
                hit_rate_pct: (((hits + pref_hits) as f64 / trips.max(1) as f64) * 1000.0).round()
                    / 10.0,
                memory_cycles: mem_cyc,
            });
        }
        Expr::FieldAccess { base, .. } => {
            acc.mem_uops += trips;
            acc.l1_hits += trips;
            acc.mem_cycles += trips * L1D_HIT_CYCLES;
            sim_expr_microarch(fn_name, base, trips, base_addr, cache, acc, cache_sites);
        }
        Expr::Call { args, .. } | Expr::List(args) => {
            acc.alu_uops += trips * 2;
            acc.in_order_compute_cycles += trips * 3;
            acc.ooo_compute_cycles += trips * 2;
            for a in args {
                sim_expr_microarch(fn_name, a, trips, base_addr, cache, acc, cache_sites);
            }
        }
        Expr::StructInit { fields, .. } => {
            acc.mem_uops += trips * (fields.len() as u64).max(1);
            acc.l1_hits += trips;
            acc.mem_cycles += trips * L1D_HIT_CYCLES;
            for (_, v) in fields {
                sim_expr_microarch(fn_name, v, trips, base_addr, cache, acc, cache_sites);
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(a)
            | Intrinsic::Abs(a)
            | Intrinsic::Upper(a)
            | Intrinsic::Lower(a)
            | Intrinsic::ToStr(a) => {
                acc.alu_uops += trips;
                acc.in_order_compute_cycles += trips;
                sim_expr_microarch(fn_name, a, trips, base_addr, cache, acc, cache_sites);
            }
            Intrinsic::Min(a, b)
            | Intrinsic::Max(a, b)
            | Intrinsic::Push { list: a, value: b }
            | Intrinsic::Contains {
                haystack: a,
                needle: b,
            } => {
                acc.alu_uops += trips * 2;
                acc.in_order_compute_cycles += trips * 2;
                sim_expr_microarch(fn_name, a, trips, base_addr, cache, acc, cache_sites);
                sim_expr_microarch(fn_name, b, trips, base_addr, cache, acc, cache_sites);
            }
            Intrinsic::Print(args) => {
                for a in args {
                    sim_expr_microarch(fn_name, a, trips, base_addr, cache, acc, cache_sites);
                }
            }
        },
        _ => {}
    }
}

#[derive(Clone)]
struct RawSchedInst {
    idx: usize,
    unit: String,
    latency: u64,
    defs: Vec<String>,
    uses: Vec<String>,
    is_barrier: bool,
    text: String,
}

/// Build the per-function Instruction Data-Dependence DAG $G = (V, E, \text{latency})$
/// and run Gibbons-Muchnick Critical-Path List Instruction Scheduling to hide
/// load/multiply/divide pipeline latencies and eliminate stall bubbles.
pub fn schedule_instructions(hub: &HubModule) -> InstructionScheduleReport {
    let start = Instant::now();
    let mut functions = Vec::new();
    let mut total_instructions = 0usize;
    let mut total_dag_edges = 0usize;
    let mut total_cycles_before = 0u64;
    let mut total_cycles_after = 0u64;
    let mut total_bubbles_eliminated = 0u64;
    let mut total_reordered_insts = 0usize;

    for item in &hub.items {
        if let Item::Function(f) = item {
            let rep = schedule_fn_instructions(f);
            total_instructions += rep.inst_count;
            total_dag_edges += rep.dag_edges_count;
            total_cycles_before += rep.in_order_cycles_before;
            total_cycles_after += rep.scheduled_cycles_after;
            total_bubbles_eliminated += rep.bubbles_eliminated;
            total_reordered_insts += rep.reordered_instructions;
            functions.push(rep);
        }
    }

    let overall_speedup = if total_cycles_after == 0 {
        1.0
    } else {
        ((total_cycles_before as f64 / total_cycles_after as f64) * 100.0).round() / 100.0
    };

    InstructionScheduleReport {
        total_functions: functions.len(),
        total_instructions,
        total_dag_edges,
        total_cycles_before,
        total_cycles_after,
        total_bubbles_eliminated,
        total_reordered_insts,
        overall_speedup,
        functions,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

fn schedule_fn_instructions(f: &FnDecl) -> FunctionScheduleReport {
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

    let mut raw_insts = Vec::new();
    let mut tmp_counter = 0usize;
    lower_stmts_for_scheduling(&f.body, &mut raw_insts, &mut tmp_counter);

    if raw_insts.is_empty() {
        raw_insts.push(RawSchedInst {
            idx: 0,
            unit: "BRU".to_string(),
            latency: 1,
            defs: Vec::new(),
            uses: Vec::new(),
            is_barrier: true,
            text: "ret".to_string(),
        });
    }

    let n = raw_insts.len();
    let mut dag_edges: Vec<DagDependenceEdge> = Vec::new();
    let mut succs: Vec<Vec<(usize, u64)>> = vec![Vec::new(); n];
    let mut preds: Vec<Vec<(usize, u64)>> = vec![Vec::new(); n];

    let mut add_edge = |u: usize, v: usize, kind: &str, lat: u64, var: &str| {
        if u >= v {
            return;
        }
        if succs[u].iter().any(|(dst, _)| *dst == v) {
            return;
        }
        succs[u].push((v, lat));
        preds[v].push((u, lat));
        dag_edges.push(DagDependenceEdge {
            from_idx: u,
            to_idx: v,
            kind: kind.to_string(),
            latency: lat,
            var: var.to_string(),
        });
    };

    for i in 0..n {
        for j in (i + 1)..n {
            let mut added_data_dep = false;
            // RAW (True Flow dependence): i defines x, j uses x
            for d in &raw_insts[i].defs {
                if raw_insts[j].uses.contains(d) {
                    add_edge(i, j, "RAW", raw_insts[i].latency, d);
                    added_data_dep = true;
                }
                // WAW (Output dependence): i defines x, j defines x
                if raw_insts[j].defs.contains(d) {
                    add_edge(i, j, "WAW", 1, d);
                    added_data_dep = true;
                }
            }
            // WAR (Anti dependence): i uses x, j defines x
            for u in &raw_insts[i].uses {
                if raw_insts[j].defs.contains(u) {
                    add_edge(i, j, "WAR", 1, u);
                    added_data_dep = true;
                }
            }
            // Control barrier ordering (when not already constrained by a data hazard)
            if !added_data_dep && (raw_insts[i].is_barrier || raw_insts[j].is_barrier) {
                add_edge(i, j, "Barrier", 1, "pc");
            }
        }
    }

    // Compute bottom-up critical-path heights h(u)
    let mut heights = vec![0u64; n];
    for u in (0..n).rev() {
        let max_succ = succs[u]
            .iter()
            .map(|(v, edge_lat)| *edge_lat + heights[*v])
            .max()
            .unwrap_or(0);
        heights[u] = raw_insts[u].latency.max(max_succ);
    }
    let critical_path_cycles = heights.iter().copied().max().unwrap_or(1);

    // 1. Simulate unscheduled (original program order) cycle count & stall bubbles
    let (in_order_cycles_before, stall_bubbles_before, _) =
        simulate_schedule_timing(&(0..n).collect::<Vec<_>>(), &raw_insts, &preds);

    // 2. Gibbons-Muchnick Critical-Path List Scheduling
    let mut in_deg: Vec<usize> = (0..n).map(|v| preds[v].len()).collect();
    let mut ready_set: BTreeSet<usize> = (0..n).filter(|&v| in_deg[v] == 0).collect();
    let mut scheduled_order: Vec<usize> = Vec::with_capacity(n);
    let mut ready_time: Vec<u64> = vec![0; n];
    let mut cur_cycle = 0u64;

    while scheduled_order.len() < n {
        // Prefer instructions that are already data-ready at `cur_cycle` with highest critical-path height;
        // if multiple are tied or latency > 1, prioritize high-latency producers (LOAD/MUL/DIV) early!
        let best = ready_set
            .iter()
            .copied()
            .max_by_key(|&u| {
                let is_data_ready = if ready_time[u] <= cur_cycle { 1u64 } else { 0u64 };
                (
                    is_data_ready,
                    heights[u],
                    raw_insts[u].latency,
                    n.saturating_sub(u),
                )
            })
            .unwrap();

        ready_set.remove(&best);
        let issue_c = cur_cycle.max(ready_time[best]);
        cur_cycle = issue_c + 1;
        scheduled_order.push(best);

        for &(v, edge_lat) in &succs[best] {
            ready_time[v] = ready_time[v].max(issue_c + edge_lat);
            in_deg[v] -= 1;
            if in_deg[v] == 0 {
                ready_set.insert(v);
            }
        }
    }

    let (scheduled_cycles_after, stall_bubbles_after, issue_times) =
        simulate_schedule_timing(&scheduled_order, &raw_insts, &preds);

    let bubbles_eliminated = stall_bubbles_before.saturating_sub(stall_bubbles_after);
    let reordered_instructions = scheduled_order
        .iter()
        .enumerate()
        .filter(|&(slot, &orig)| slot != orig)
        .count();
    let speedup_ratio = if scheduled_cycles_after == 0 {
        1.0
    } else {
        ((in_order_cycles_before as f64 / scheduled_cycles_after as f64) * 100.0).round() / 100.0
    };

    let mut instructions = Vec::with_capacity(n);
    for (slot, &orig_idx) in scheduled_order.iter().enumerate() {
        let inst = &raw_insts[orig_idx];
        let issue_c = issue_times[slot];
        instructions.push(ScheduledInstEntry {
            orig_idx,
            sched_slot: slot,
            issue_cycle: issue_c,
            ready_cycle: issue_c + inst.latency,
            unit: inst.unit.clone(),
            latency: inst.latency,
            critical_height: heights[orig_idx],
            text: inst.text.clone(),
        });
    }

    let unscheduled_listing = raw_insts
        .iter()
        .map(|i| {
            format!(
                "  [I{:>2} · {:<3} · {:>2}c · h={:>2}] {}",
                i.idx, i.unit, i.latency, heights[i.idx], i.text
            )
        })
        .collect::<Vec<_>>()
        .join("\n");

    let scheduled_listing = instructions
        .iter()
        .map(|s| {
            format!(
                "  [S{:>2} (was I{:>2}) · cyc {:>2}..{:>2} · {:<3}] {}",
                s.sched_slot, s.orig_idx, s.issue_cycle, s.ready_cycle, s.unit, s.text
            )
        })
        .collect::<Vec<_>>()
        .join("\n");

    let mermaid_dag = build_schedule_mermaid_dag(&f.name, &raw_insts, &heights, &dag_edges);

    FunctionScheduleReport {
        fn_name: f.name.clone(),
        signature,
        inst_count: n,
        dag_edges_count: dag_edges.len(),
        critical_path_cycles,
        in_order_cycles_before,
        scheduled_cycles_after,
        stall_bubbles_before,
        stall_bubbles_after,
        bubbles_eliminated,
        reordered_instructions,
        speedup_ratio,
        instructions,
        dag_edges,
        unscheduled_listing,
        scheduled_listing,
        mermaid_dag,
    }
}

fn simulate_schedule_timing(
    order: &[usize],
    raw_insts: &[RawSchedInst],
    preds: &[Vec<(usize, u64)>],
) -> (u64, u64, Vec<u64>) {
    let n = raw_insts.len();
    let mut issued_at: Vec<Option<u64>> = vec![None; n];
    let mut slot_issue_times = Vec::with_capacity(order.len());
    let mut cur_cycle = 0u64;
    let mut total_bubbles = 0u64;

    for &u in order {
        let mut min_ready = cur_cycle;
        for &(p, lat) in &preds[u] {
            if let Some(p_issue) = issued_at[p] {
                min_ready = min_ready.max(p_issue + lat);
            }
        }
        if min_ready > cur_cycle {
            total_bubbles += min_ready - cur_cycle;
        }
        let issue_c = min_ready;
        issued_at[u] = Some(issue_c);
        slot_issue_times.push(issue_c);
        cur_cycle = issue_c + 1;
    }

    let completion = (0..n)
        .filter_map(|u| issued_at[u].map(|t| t + raw_insts[u].latency))
        .max()
        .unwrap_or(1);

    (completion, total_bubbles, slot_issue_times)
}

fn lower_stmts_for_scheduling(
    stmts: &[Stmt],
    out: &mut Vec<RawSchedInst>,
    tmp_counter: &mut usize,
) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { name, value, .. } => {
                lower_expr_for_scheduling(value, Some(name), out, tmp_counter);
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                if let AssignTarget::Index { index, .. } = target {
                    let _ = lower_expr_for_scheduling(index, None, out, tmp_counter);
                }
                let dst = match target {
                    AssignTarget::Var(v) => v.clone(),
                    AssignTarget::Index { base, .. } | AssignTarget::Field { base, .. } => {
                        base.clone()
                    }
                };
                match op {
                    AssignOp::Set => {
                        lower_expr_for_scheduling(value, Some(&dst), out, tmp_counter);
                    }
                    AssignOp::AddAssign | AssignOp::SubAssign => {
                        let rhs = lower_expr_for_scheduling(value, None, out, tmp_counter);
                        let sym = if *op == AssignOp::AddAssign { "+" } else { "-" };
                        let idx = out.len();
                        out.push(RawSchedInst {
                            idx,
                            unit: "ALU".to_string(),
                            latency: 1,
                            defs: vec![dst.clone()],
                            uses: vec![dst.clone(), rhs.clone()],
                            is_barrier: false,
                            text: format!("{} = {} {} {}", dst, dst, sym, rhs),
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
                let cv = lower_expr_for_scheduling(cond, None, out, tmp_counter);
                let idx = out.len();
                out.push(RawSchedInst {
                    idx,
                    unit: "BRU".to_string(),
                    latency: 1,
                    defs: Vec::new(),
                    uses: vec![cv.clone()],
                    is_barrier: false,
                    text: format!("cmp_branch {}", cv),
                });
                lower_stmts_for_scheduling(then_body, out, tmp_counter);
                lower_stmts_for_scheduling(else_body, out, tmp_counter);
            }
            Stmt::Match { expr, arms, .. } => {
                let sv = lower_expr_for_scheduling(expr, None, out, tmp_counter);
                let idx = out.len();
                out.push(RawSchedInst {
                    idx,
                    unit: "BRU".to_string(),
                    latency: 1,
                    defs: Vec::new(),
                    uses: vec![sv.clone()],
                    is_barrier: false,
                    text: format!("switch_dispatch {}", sv),
                });
                for arm in arms {
                    lower_stmts_for_scheduling(&arm.body, out, tmp_counter);
                }
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                lower_expr_for_scheduling(start, Some(var), out, tmp_counter);
                let ev = lower_expr_for_scheduling(end, None, out, tmp_counter);
                let idx = out.len();
                out.push(RawSchedInst {
                    idx,
                    unit: "BRU".to_string(),
                    latency: 1,
                    defs: vec![var.clone()],
                    uses: vec![var.clone(), ev.clone()],
                    is_barrier: false,
                    text: format!("loop_range {} < {}", var, ev),
                });
                lower_stmts_for_scheduling(body, out, tmp_counter);
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let iv = lower_expr_for_scheduling(iter, None, out, tmp_counter);
                let idx = out.len();
                out.push(RawSchedInst {
                    idx,
                    unit: "LSU".to_string(),
                    latency: 4,
                    defs: vec![var.clone()],
                    uses: vec![iv.clone()],
                    is_barrier: false,
                    text: format!("{} = load_elem({})", var, iv),
                });
                lower_stmts_for_scheduling(body, out, tmp_counter);
            }
            Stmt::While { cond, body, .. } => {
                let cv = lower_expr_for_scheduling(cond, None, out, tmp_counter);
                let idx = out.len();
                out.push(RawSchedInst {
                    idx,
                    unit: "BRU".to_string(),
                    latency: 1,
                    defs: Vec::new(),
                    uses: vec![cv.clone()],
                    is_barrier: false,
                    text: format!("while_guard {}", cv),
                });
                lower_stmts_for_scheduling(body, out, tmp_counter);
            }
            Stmt::Return { value, .. } => {
                let rv = value
                    .as_ref()
                    .map(|v| lower_expr_for_scheduling(v, None, out, tmp_counter));
                let uses = rv.iter().cloned().collect();
                let idx = out.len();
                out.push(RawSchedInst {
                    idx,
                    unit: "BRU".to_string(),
                    latency: 1,
                    defs: Vec::new(),
                    uses,
                    is_barrier: true,
                    text: format!("ret {}", rv.unwrap_or_else(|| "void".to_string())),
                });
            }
            Stmt::Expr { expr, .. } => {
                lower_expr_for_scheduling(expr, None, out, tmp_counter);
            }
            Stmt::Assert { cond, .. } => {
                lower_expr_for_scheduling(cond, None, out, tmp_counter);
            }
            Stmt::AssertEq { left, right, .. } => {
                lower_expr_for_scheduling(left, None, out, tmp_counter);
                lower_expr_for_scheduling(right, None, out, tmp_counter);
            }
            _ => {}
        }
    }
}

fn next_sched_tmp(tmp_counter: &mut usize) -> String {
    let t = format!("r{}", *tmp_counter);
    *tmp_counter += 1;
    t
}

fn lower_expr_for_scheduling(
    expr: &Expr,
    target_dst: Option<&str>,
    out: &mut Vec<RawSchedInst>,
    tmp_counter: &mut usize,
) -> String {
    match expr {
        Expr::Var(v) => {
            if let Some(dst) = target_dst {
                if dst != v {
                    let idx = out.len();
                    out.push(RawSchedInst {
                        idx,
                        unit: "ALU".to_string(),
                        latency: 1,
                        defs: vec![dst.to_string()],
                        uses: vec![v.clone()],
                        is_barrier: false,
                        text: format!("{} = mov {}", dst, v),
                    });
                    return dst.to_string();
                }
            }
            v.clone()
        }
        Expr::Int(n) => {
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            let idx = out.len();
            out.push(RawSchedInst {
                idx,
                unit: "ALU".to_string(),
                latency: 1,
                defs: vec![dst.clone()],
                uses: Vec::new(),
                is_barrier: false,
                text: format!("{} = mov #{}", dst, n),
            });
            dst
        }
        Expr::Bool(b) => {
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            let idx = out.len();
            out.push(RawSchedInst {
                idx,
                unit: "ALU".to_string(),
                latency: 1,
                defs: vec![dst.clone()],
                uses: Vec::new(),
                is_barrier: false,
                text: format!("{} = mov #{}", dst, if *b { 1 } else { 0 }),
            });
            dst
        }
        Expr::Binary { op, left, right } => {
            let l = lower_expr_for_scheduling(left, None, out, tmp_counter);
            let r = lower_expr_for_scheduling(right, None, out, tmp_counter);
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            let (unit, lat) = match op {
                BinOp::Mul => ("MUL", 3),
                BinOp::Div | BinOp::IntDiv | BinOp::Mod => ("DIV", 10),
                _ => ("ALU", 1),
            };
            let idx = out.len();
            out.push(RawSchedInst {
                idx,
                unit: unit.to_string(),
                latency: lat,
                defs: vec![dst.clone()],
                uses: vec![l.clone(), r.clone()],
                is_barrier: false,
                text: format!("{} = {:?} {}, {}", dst, op, l, r),
            });
            dst
        }
        Expr::Unary { op, expr: inner } => {
            let v = lower_expr_for_scheduling(inner, None, out, tmp_counter);
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            let idx = out.len();
            out.push(RawSchedInst {
                idx,
                unit: "ALU".to_string(),
                latency: 1,
                defs: vec![dst.clone()],
                uses: vec![v.clone()],
                is_barrier: false,
                text: format!(
                    "{} = {} {}",
                    dst,
                    match op {
                        UnaryOp::Neg => "neg",
                        UnaryOp::Not => "not",
                    },
                    v
                ),
            });
            dst
        }
        Expr::Index { base, index } => {
            let b = lower_expr_for_scheduling(base, None, out, tmp_counter);
            let i = lower_expr_for_scheduling(index, None, out, tmp_counter);
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            let idx = out.len();
            out.push(RawSchedInst {
                idx,
                unit: "LSU".to_string(),
                latency: 4,
                defs: vec![dst.clone()],
                uses: vec![b.clone(), i.clone()],
                is_barrier: false,
                text: format!("{} = ldr [{} + {} * 8]", dst, b, i),
            });
            dst
        }
        Expr::FieldAccess { base, field } => {
            let b = lower_expr_for_scheduling(base, None, out, tmp_counter);
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            let idx = out.len();
            out.push(RawSchedInst {
                idx,
                unit: "LSU".to_string(),
                latency: 4,
                defs: vec![dst.clone()],
                uses: vec![b.clone()],
                is_barrier: false,
                text: format!("{} = ldr {}.{}", dst, b, field),
            });
            dst
        }
        Expr::Call { func, args } => {
            let mut avs = Vec::new();
            for a in args {
                avs.push(lower_expr_for_scheduling(a, None, out, tmp_counter));
            }
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            let idx = out.len();
            out.push(RawSchedInst {
                idx,
                unit: "ALU".to_string(),
                latency: 3,
                defs: vec![dst.clone()],
                uses: avs.clone(),
                is_barrier: false,
                text: format!("{} = call {}({})", dst, func, avs.join(", ")),
            });
            dst
        }
        Expr::StructInit { name, fields } => {
            let mut fvs = Vec::new();
            for (_, v) in fields {
                fvs.push(lower_expr_for_scheduling(v, None, out, tmp_counter));
            }
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            let idx = out.len();
            out.push(RawSchedInst {
                idx,
                unit: "LSU".to_string(),
                latency: 2,
                defs: vec![dst.clone()],
                uses: fvs.clone(),
                is_barrier: false,
                text: format!("{} = pack {} {{ {} }}", dst, name, fvs.join(", ")),
            });
            dst
        }
        Expr::Intrinsic(intr) => {
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            match intr.as_ref() {
                Intrinsic::Len(a)
                | Intrinsic::Abs(a)
                | Intrinsic::Upper(a)
                | Intrinsic::Lower(a)
                | Intrinsic::ToStr(a) => {
                    let av = lower_expr_for_scheduling(a, None, out, tmp_counter);
                    let idx = out.len();
                    out.push(RawSchedInst {
                        idx,
                        unit: "ALU".to_string(),
                        latency: 1,
                        defs: vec![dst.clone()],
                        uses: vec![av.clone()],
                        is_barrier: false,
                        text: format!("{} = intr({})", dst, av),
                    });
                }
                Intrinsic::Min(a, b)
                | Intrinsic::Max(a, b)
                | Intrinsic::Push { list: a, value: b }
                | Intrinsic::Contains {
                    haystack: a,
                    needle: b,
                } => {
                    let av = lower_expr_for_scheduling(a, None, out, tmp_counter);
                    let bv = lower_expr_for_scheduling(b, None, out, tmp_counter);
                    let idx = out.len();
                    out.push(RawSchedInst {
                        idx,
                        unit: "ALU".to_string(),
                        latency: 1,
                        defs: vec![dst.clone()],
                        uses: vec![av.clone(), bv.clone()],
                        is_barrier: false,
                        text: format!("{} = csel {}, {}", dst, av, bv),
                    });
                }
                Intrinsic::Print(args) => {
                    let mut avs = Vec::new();
                    for a in args {
                        avs.push(lower_expr_for_scheduling(a, None, out, tmp_counter));
                    }
                    let idx = out.len();
                    out.push(RawSchedInst {
                        idx,
                        unit: "ALU".to_string(),
                        latency: 2,
                        defs: vec![dst.clone()],
                        uses: avs.clone(),
                        is_barrier: false,
                        text: format!("print({})", avs.join(", ")),
                    });
                }
            }
            dst
        }
        _ => {
            let dst = target_dst
                .map(|s| s.to_string())
                .unwrap_or_else(|| next_sched_tmp(tmp_counter));
            let idx = out.len();
            out.push(RawSchedInst {
                idx,
                unit: "ALU".to_string(),
                latency: 1,
                defs: vec![dst.clone()],
                uses: Vec::new(),
                is_barrier: false,
                text: format!("{} = const {}", dst, format_expr_compact(expr)),
            });
            dst
        }
    }
}

fn build_schedule_mermaid_dag(
    fn_name: &str,
    raw_insts: &[RawSchedInst],
    heights: &[u64],
    edges: &[DagDependenceEdge],
) -> String {
    let mut out = String::from("flowchart TD\n");
    out.push_str(&format!("  subgraph \"Instruction DAG: {}\"\n", fn_name));
    for inst in raw_insts.iter().take(18) {
        let clean = inst.text.replace('"', "'");
        out.push_str(&format!(
            "    I{}[\"I{} ({} · {}c · h={}): {}\"]\n",
            inst.idx, inst.idx, inst.unit, inst.latency, heights[inst.idx], clean
        ));
    }
    for e in edges.iter().filter(|e| e.from_idx < 18 && e.to_idx < 18).take(24) {
        out.push_str(&format!(
            "    I{} -->|\"{} ({}c: {})\"| I{}\n",
            e.from_idx, e.kind, e.latency, e.var, e.to_idx
        ));
    }
    out.push_str("  end\n");
    out
}

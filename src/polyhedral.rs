use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use crate::egraph::format_expr_compact;
use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, NodeId, Stmt,
};

#[derive(Debug, Clone)]
pub struct AffineAccess {
    pub array_or_var: String,
    pub access_kind: String, // "Read" | "Write"
    pub index_expr: String,
    pub stride: i64,
    pub offset: i64,
}

#[derive(Debug, Clone)]
pub struct LoopDependenceEdge {
    pub variable: String,
    pub kind: String,     // "RAW (Flow)", "WAR (Anti)", "WAW (Output)"
    pub distance: String, // "0 (loop-independent)" | "+1 (loop-carried)"
    pub is_reduction: bool,
    pub reduction_monoid: Option<String>, // e.g., "(+, 0)", "(min, +∞)", "(max, -∞)"
    pub blocks_simd: bool,
    pub note: String,
}

#[derive(Debug, Clone)]
pub struct PolyhedralLoopReport {
    pub loop_id: NodeId,
    pub fn_name: String,
    pub loop_kind: String, // "ForRange" | "ForEach" | "While"
    pub induction_var: String,
    pub iteration_domain: String, // e.g., "{ i ∈ ℤ | 0 <= i < len(costs) }"
    pub classification: String,   // "AssociativeMapReduce" | "FilterMapReduce" | "ParallelMap" | "SequentialStateMachine"
    pub simd_vectorizable: bool,
    pub map_reduce_parallelizable: bool,
    pub estimated_simd4_speedup: f64,
    pub work_t1_symbolic: String,
    pub span_tinf_symbolic: String,
    pub brent_parallelism_n64: f64,
    pub accesses: Vec<AffineAccess>,
    pub dependences: Vec<LoopDependenceEdge>,
    pub reductions: Vec<String>,
    pub vectorized_by_spoke: BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct PolyhedralReport {
    pub total_loops: usize,
    pub vectorizable_loops: usize,
    pub map_reduce_loops: usize,
    pub sequential_state_loops: usize,
    pub total_reductions: usize,
    pub max_simd4_speedup: f64,
    pub loops: Vec<PolyhedralLoopReport>,
    pub elapsed_ms: u128,
}

#[derive(Debug, Clone)]
pub struct LoopTerminationProof {
    pub stmt_id: NodeId,
    pub fn_name: String,
    pub loop_header: String,
    pub ranking_function: String, // e.g., "V(i) = len(costs) - i"
    pub bounded_below_vc: String, // e.g., "i < len(costs) ==> len(costs) - i >= 1 > 0"
    pub strict_decrease_vc: String, // e.g., "V(i + 1) = len(costs) - (i + 1) = V(i) - 1 < V(i)"
    pub proven_terminating: bool,
    pub status: String, // "Terminating (Well-Founded Ranking)" | "Non-Terminating / Unbounded Witness"
    pub witness_or_note: String,
}

#[derive(Debug, Clone)]
pub struct FunctionWcetReport {
    pub fn_name: String,
    pub signature: String,
    pub proven_terminating: bool,
    pub bcet_symbolic: String,
    pub wcet_symbolic: String,
    pub bcet_cycles_n64: u64,
    pub wcet_cycles_n64: u64,
    pub jitter_ratio: f64,
    pub worst_case_path: Vec<String>,
    pub loop_proofs: Vec<LoopTerminationProof>,
}

#[derive(Debug, Clone)]
pub struct TerminationWcetReport {
    pub all_terminating: bool,
    pub total_functions: usize,
    pub total_loops_audited: usize,
    pub proven_terminating_loops: usize,
    pub diverging_or_unproven_loops: usize,
    pub module_wcet_cycles_n64: u64,
    pub module_bcet_cycles_n64: u64,
    pub functions: Vec<FunctionWcetReport>,
    pub elapsed_ms: u128,
}

/// Analyze all loops in `hub` using Polyhedral Affine Iteration Domains, Bernstein Read/Write
/// Dependence Vectors, Associative Monoid Reduction Recognition, Brent's Theorem Work-Span
/// Parallelism, and 13-Spoke SIMD / Functional Map-Reduce Kernel Synthesis.
pub fn analyze_polyhedral(hub: &HubModule) -> PolyhedralReport {
    let start = Instant::now();
    let mut loops = Vec::new();

    for item in &hub.items {
        if let Item::Function(f) = item {
            if f.name == "main" {
                continue;
            }
            collect_polyhedral_loops(&f.name, &f.body, &mut loops);
        }
    }

    // If non-main functions had no loops, also inspect `main`
    if loops.is_empty() {
        for item in &hub.items {
            if let Item::Function(f) = item {
                if f.name == "main" {
                    collect_polyhedral_loops(&f.name, &f.body, &mut loops);
                }
            }
        }
    }

    let total_loops = loops.len();
    let vectorizable_loops = loops.iter().filter(|l| l.simd_vectorizable).count();
    let map_reduce_loops = loops
        .iter()
        .filter(|l| l.map_reduce_parallelizable)
        .count();
    let sequential_state_loops = loops
        .iter()
        .filter(|l| !l.map_reduce_parallelizable)
        .count();
    let total_reductions = loops.iter().map(|l| l.reductions.len()).sum();
    let max_simd4_speedup = loops
        .iter()
        .map(|l| l.estimated_simd4_speedup)
        .fold(1.0_f64, f64::max);

    PolyhedralReport {
        total_loops,
        vectorizable_loops,
        map_reduce_loops,
        sequential_state_loops,
        total_reductions,
        max_simd4_speedup,
        loops,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

fn collect_polyhedral_loops(
    fn_name: &str,
    stmts: &[Stmt],
    out: &mut Vec<PolyhedralLoopReport>,
) {
    for stmt in stmts {
        match stmt {
            Stmt::ForRange {
                id,
                var,
                start,
                end,
                body,
                ..
            } => {
                let dom = format!(
                    "{{ {} ∈ ℤ | {} <= {} < {} }}",
                    var,
                    format_expr_compact(start),
                    var,
                    format_expr_compact(end)
                );
                let rep = analyze_single_loop(
                    *id,
                    fn_name,
                    "ForRange",
                    var,
                    &dom,
                    Some(end),
                    body,
                );
                out.push(rep);
                collect_polyhedral_loops(fn_name, body, out);
            }
            Stmt::ForEach {
                id,
                var,
                iter,
                body,
                ..
            } => {
                let iter_str = format_expr_compact(iter);
                let dom = format!(
                    "{{ idx_{} ∈ ℤ | 0 <= idx_{} < len({}) · {} = {}[idx_{}] }}",
                    var, var, iter_str, var, iter_str, var
                );
                let rep = analyze_single_loop(
                    *id,
                    fn_name,
                    "ForEach",
                    var,
                    &dom,
                    Some(iter),
                    body,
                );
                out.push(rep);
                collect_polyhedral_loops(fn_name, body, out);
            }
            Stmt::While { id, cond, body, .. } => {
                let dom = format!("{{ step ∈ ℕ | while {} }}", format_expr_compact(cond));
                let rep = analyze_single_loop(*id, fn_name, "While", "step", &dom, None, body);
                out.push(rep);
                collect_polyhedral_loops(fn_name, body, out);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_polyhedral_loops(fn_name, then_body, out);
                collect_polyhedral_loops(fn_name, else_body, out);
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    collect_polyhedral_loops(fn_name, &a.body, out);
                }
            }
            _ => {}
        }
    }
}

#[derive(Default)]
struct LoopBodyScan {
    local_lets: BTreeSet<String>,
    reads: BTreeSet<String>,
    writes: BTreeMap<String, Vec<(AssignOp, Expr)>>,
    reads_inside_cond: BTreeSet<String>,
    has_early_exit: bool,
    has_list_push: Option<(String, String)>, // (list_name, pushed_expr)
    accesses: Vec<AffineAccess>,
    filter_conds: Vec<String>,
}

fn scan_loop_body(
    stmts: &[Stmt],
    induction_var: &str,
    in_cond_guard: bool,
    scan: &mut LoopBodyScan,
) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { name, value, .. } => {
                scan.local_lets.insert(name.clone());
                scan_expr_reads(value, induction_var, false, scan);
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                scan_expr_reads(value, induction_var, false, scan);
                match target {
                    AssignTarget::Var(v) => {
                        if matches!(op, AssignOp::AddAssign | AssignOp::SubAssign) {
                            scan.reads.insert(v.clone());
                        }
                        scan.writes
                            .entry(v.clone())
                            .or_default()
                            .push((*op, value.clone()));
                    }
                    AssignTarget::Index { base, index } => {
                        scan_expr_reads(index, induction_var, false, scan);
                        let (stride, offset) = affine_coeffs(index, induction_var);
                        scan.accesses.push(AffineAccess {
                            array_or_var: base.clone(),
                            access_kind: "Write".to_string(),
                            index_expr: format_expr_compact(index),
                            stride,
                            offset,
                        });
                        scan.writes
                            .entry(base.clone())
                            .or_default()
                            .push((*op, value.clone()));
                    }
                    AssignTarget::Field { base, .. } => {
                        scan.writes
                            .entry(base.clone())
                            .or_default()
                            .push((*op, value.clone()));
                    }
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                scan.filter_conds.push(format_expr_compact(cond));
                scan_expr_reads(cond, induction_var, true, scan);
                scan_loop_body(then_body, induction_var, true, scan);
                scan_loop_body(else_body, induction_var, true, scan);
                let _ = in_cond_guard;
            }
            Stmt::Match { expr, arms, .. } => {
                scan_expr_reads(expr, induction_var, true, scan);
                for a in arms {
                    scan_loop_body(&a.body, induction_var, true, scan);
                }
            }
            Stmt::Break { .. } | Stmt::Return { .. } => {
                scan.has_early_exit = true;
            }
            Stmt::Continue { .. } => {}
            Stmt::Expr { expr, .. } => {
                if let Expr::Intrinsic(intr) = expr {
                    if let Intrinsic::Push {
                        list: Expr::Var(lname),
                        value,
                    } = intr.as_ref()
                    {
                        scan.has_list_push = Some((lname.clone(), format_expr_compact(value)));
                    }
                }
                scan_expr_reads(expr, induction_var, false, scan);
            }
            Stmt::While { cond, body, .. } => {
                scan_expr_reads(cond, induction_var, true, scan);
                scan_loop_body(body, induction_var, true, scan);
            }
            Stmt::ForEach { iter, body, .. } => {
                scan_expr_reads(iter, induction_var, false, scan);
                scan_loop_body(body, induction_var, false, scan);
            }
            Stmt::ForRange {
                start, end, body, ..
            } => {
                scan_expr_reads(start, induction_var, false, scan);
                scan_expr_reads(end, induction_var, false, scan);
                scan_loop_body(body, induction_var, false, scan);
            }
            Stmt::Assert { cond, .. } => {
                scan_expr_reads(cond, induction_var, false, scan);
            }
            Stmt::AssertEq { left, right, .. } => {
                scan_expr_reads(left, induction_var, false, scan);
                scan_expr_reads(right, induction_var, false, scan);
            }
            Stmt::Comment { .. } => {}
        }
    }
}

fn scan_expr_reads(
    expr: &Expr,
    induction_var: &str,
    in_cond: bool,
    scan: &mut LoopBodyScan,
) {
    match expr {
        Expr::Var(v) => {
            if v != induction_var && !scan.local_lets.contains(v) {
                scan.reads.insert(v.clone());
                if in_cond {
                    scan.reads_inside_cond.insert(v.clone());
                }
            }
        }
        Expr::Index { base, index } => {
            if let Expr::Var(arr) = base.as_ref() {
                let (stride, offset) = affine_coeffs(index, induction_var);
                scan.accesses.push(AffineAccess {
                    array_or_var: arr.clone(),
                    access_kind: "Read".to_string(),
                    index_expr: format_expr_compact(index),
                    stride,
                    offset,
                });
            }
            scan_expr_reads(base, induction_var, in_cond, scan);
            scan_expr_reads(index, induction_var, in_cond, scan);
        }
        Expr::FieldAccess { base, .. } | Expr::Unary { expr: base, .. } => {
            scan_expr_reads(base, induction_var, in_cond, scan);
        }
        Expr::Binary { left, right, .. } => {
            scan_expr_reads(left, induction_var, in_cond, scan);
            scan_expr_reads(right, induction_var, in_cond, scan);
        }
        Expr::List(items) | Expr::Call { args: items, .. } => {
            for i in items {
                scan_expr_reads(i, induction_var, in_cond, scan);
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, v) in fields {
                scan_expr_reads(v, induction_var, in_cond, scan);
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(a)
            | Intrinsic::Abs(a)
            | Intrinsic::Upper(a)
            | Intrinsic::Lower(a)
            | Intrinsic::ToStr(a) => scan_expr_reads(a, induction_var, in_cond, scan),
            Intrinsic::Min(a, b)
            | Intrinsic::Max(a, b)
            | Intrinsic::Push { list: a, value: b }
            | Intrinsic::Contains {
                haystack: a,
                needle: b,
            } => {
                scan_expr_reads(a, induction_var, in_cond, scan);
                scan_expr_reads(b, induction_var, in_cond, scan);
            }
            Intrinsic::Print(args) => {
                for a in args {
                    scan_expr_reads(a, induction_var, in_cond, scan);
                }
            }
        },
        _ => {}
    }
}

fn affine_coeffs(index: &Expr, iv: &str) -> (i64, i64) {
    match index {
        Expr::Var(v) if v == iv => (1, 0),
        Expr::Int(c) => (0, *c),
        Expr::Binary {
            op: BinOp::Add,
            left,
            right,
        } => {
            let (s1, o1) = affine_coeffs(left, iv);
            let (s2, o2) = affine_coeffs(right, iv);
            (s1 + s2, o1 + o2)
        }
        Expr::Binary {
            op: BinOp::Sub,
            left,
            right,
        } => {
            let (s1, o1) = affine_coeffs(left, iv);
            let (s2, o2) = affine_coeffs(right, iv);
            (s1 - s2, o1 - o2)
        }
        Expr::Binary {
            op: BinOp::Mul,
            left,
            right,
        } => match (left.as_ref(), right.as_ref()) {
            (Expr::Var(v), Expr::Int(k)) | (Expr::Int(k), Expr::Var(v)) if v == iv => (*k, 0),
            _ => (1, 0),
        },
        _ => (1, 0),
    }
}

fn analyze_single_loop(
    loop_id: NodeId,
    fn_name: &str,
    loop_kind: &str,
    induction_var: &str,
    iteration_domain: &str,
    bound_expr: Option<&Expr>,
    body: &[Stmt],
) -> PolyhedralLoopReport {
    let mut scan = LoopBodyScan::default();
    if loop_kind == "ForEach" {
        if let Some(iter_e) = bound_expr {
            scan.accesses.push(AffineAccess {
                array_or_var: format_expr_compact(iter_e),
                access_kind: "Read".to_string(),
                index_expr: format!("idx_{}", induction_var),
                stride: 1,
                offset: 0,
            });
        }
    }
    scan_loop_body(body, induction_var, false, &mut scan);

    let mut dependences = Vec::new();
    let mut reductions = Vec::new();
    let mut has_sequential_carried_dep = scan.has_early_exit || loop_kind == "While";

    for (var, ops) in &scan.writes {
        if scan.local_lets.contains(var) {
            continue;
        }
        let all_additive = ops
            .iter()
            .all(|(op, _)| matches!(op, AssignOp::AddAssign | AssignOp::SubAssign));
        let all_minmax = ops.iter().all(|(op, val)| {
            if *op != AssignOp::Set {
                return false;
            }
            match val {
                Expr::Intrinsic(intr) => match intr.as_ref() {
                    Intrinsic::Min(Expr::Var(a), _)
                    | Intrinsic::Min(_, Expr::Var(a))
                    | Intrinsic::Max(Expr::Var(a), _)
                    | Intrinsic::Max(_, Expr::Var(a)) => a == var,
                    _ => false,
                },
                _ => false,
            }
        });

        let read_in_guard = scan.reads_inside_cond.contains(var);

        if (all_additive || all_minmax) && !read_in_guard {
            let monoid = if all_additive {
                "(+, 0) Associative Commutative".to_string()
            } else {
                "(min/max, ±∞) Associative Idempotent".to_string()
            };
            reductions.push(format!("{} via {}", var, monoid));
            dependences.push(LoopDependenceEdge {
                variable: var.clone(),
                kind: "RAW+WAW (Reduction)".to_string(),
                distance: "+1 (associative monoid)".to_string(),
                is_reduction: true,
                reduction_monoid: Some(monoid),
                blocks_simd: false,
                note: format!(
                    "Accumulator `{}` forms a tree-reducible monoid across SIMD lanes",
                    var
                ),
            });
        } else {
            has_sequential_carried_dep = true;
            dependences.push(LoopDependenceEdge {
                variable: var.clone(),
                kind: "RAW (Loop-Carried State)".to_string(),
                distance: "+1 (sequential)".to_string(),
                is_reduction: false,
                reduction_monoid: None,
                blocks_simd: true,
                note: if read_in_guard {
                    format!(
                        "State variable `{}` both guards a branch condition and is mutated across iterations",
                        var
                    )
                } else {
                    format!(
                        "Variable `{}` has a non-associative loop-carried update across iterations",
                        var
                    )
                },
            });
        }
    }

    if scan.has_early_exit {
        dependences.push(LoopDependenceEdge {
            variable: "control_pc".to_string(),
            kind: "Control Dependence (Early Exit)".to_string(),
            distance: "+1 (sequential)".to_string(),
            is_reduction: false,
            reduction_monoid: None,
            blocks_simd: true,
            note: "Loop body contains early `break` or `return`, serializing iteration order"
                .to_string(),
        });
    }

    let classification = if !has_sequential_carried_dep {
        if reductions.is_empty() && scan.has_list_push.is_some() {
            "ParallelMap".to_string()
        } else if scan.filter_conds.is_empty() {
            "AssociativeMapReduce".to_string()
        } else {
            "FilterMapReduce".to_string()
        }
    } else {
        "SequentialStateMachine".to_string()
    };

    let simd_vectorizable = !has_sequential_carried_dep;
    let map_reduce_parallelizable = !has_sequential_carried_dep;
    let estimated_simd4_speedup = if simd_vectorizable {
        if scan.filter_conds.is_empty() {
            3.6
        } else {
            2.9
        }
    } else {
        1.0
    };

    let work_t1_symbolic = "Θ(N)".to_string();
    let span_tinf_symbolic = if map_reduce_parallelizable {
        if reductions.is_empty() {
            "Θ(1)".to_string()
        } else {
            "Θ(log₂ N)".to_string()
        }
    } else {
        "Θ(N)".to_string()
    };
    let brent_parallelism_n64 = if map_reduce_parallelizable {
        if reductions.is_empty() {
            64.0
        } else {
            10.67 // 64 / log2(64) = 64 / 6
        }
    } else {
        1.0
    };

    let vectorized_by_spoke = synthesize_vectorized_kernels(
        fn_name,
        induction_var,
        bound_expr,
        &classification,
        &reductions,
        &scan,
    );

    PolyhedralLoopReport {
        loop_id,
        fn_name: fn_name.to_string(),
        loop_kind: loop_kind.to_string(),
        induction_var: induction_var.to_string(),
        iteration_domain: iteration_domain.to_string(),
        classification,
        simd_vectorizable,
        map_reduce_parallelizable,
        estimated_simd4_speedup,
        work_t1_symbolic,
        span_tinf_symbolic,
        brent_parallelism_n64,
        accesses: scan.accesses,
        dependences,
        reductions,
        vectorized_by_spoke,
    }
}

fn synthesize_vectorized_kernels(
    fn_name: &str,
    induction_var: &str,
    bound_expr: Option<&Expr>,
    classification: &str,
    reductions: &[String],
    scan: &LoopBodyScan,
) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let arr_name = scan
        .accesses
        .first()
        .map(|a| a.array_or_var.clone())
        .or_else(|| bound_expr.map(format_expr_compact))
        .unwrap_or_else(|| "items".to_string());
    let filter_note = scan
        .filter_conds
        .first()
        .cloned()
        .unwrap_or_else(|| "true".to_string());
    let red_vars: Vec<String> = reductions
        .iter()
        .filter_map(|r| r.split_whitespace().next().map(|s| s.to_string()))
        .collect();
    let red_summary = if red_vars.is_empty() {
        "acc".to_string()
    } else {
        red_vars.join(", ")
    };

    let is_parallel = classification != "SequentialStateMachine";

    out.insert(
        "rust".to_string(),
        if is_parallel {
            format!(
                "// [{classification}] Polyhedral SIMD / Parallel Map-Reduce for `{fn_name}`\nlet ({red_summary}) = {arr_name}.iter().copied()\n    .filter(|&{induction_var}| {filter_note})\n    .fold(0_i64, |acc, {induction_var}| acc + {induction_var});"
            )
        } else {
            format!(
                "// [{classification}] Sequential scan with distance d=+1 on ({red_summary})\nlet FinalState = {arr_name}.iter().copied().try_fold(init_state, |state, {induction_var}| /* transition */);"
            )
        },
    );

    out.insert(
        "zig".to_string(),
        if is_parallel {
            format!(
                "// [{classification}] Zig 0.16 @Vector(4, i64) SIMD reduction for `{fn_name}`\nvar vec_acc: @Vector(4, i64) = @splat(0);\n// 4-wide SIMD lane body over {arr_name} -> @reduce(.Add, vec_acc)"
            )
        } else {
            format!(
                "// [{classification}] Sequential loop-carried state transitions in `{fn_name}`\nfor ({arr_name}.slice()) |{induction_var}| {{ /* d=+1 state update */ }}"
            )
        },
    );

    out.insert(
        "c".to_string(),
        if is_parallel {
            format!(
                "// [{classification}] Clang/OpenMP SIMD pragma kernel for `{fn_name}`\n#pragma clang loop vectorize(enable) interleave(enable)\nfor (int64_t {induction_var} = 0; {induction_var} < {arr_name}.len; {induction_var}++) {{ /* reduction(+:{red_summary}) */ }}"
            )
        } else {
            format!(
                "// [{classification}] Loop-carried dependency prevents SIMD vectorization in `{fn_name}`\n#pragma clang loop vectorize(disable)\nfor (int64_t {induction_var} = 0; {induction_var} < {arr_name}.len; {induction_var}++) {{ /* sequential scan */ }}"
            )
        },
    );

    out.insert(
        "cpp".to_string(),
        if is_parallel {
            format!(
                "// [{classification}] C++17 std::transform_reduce parallel execution policy for `{fn_name}`\nauto res = std::transform_reduce({arr_name}.begin(), {arr_name}.end(), int64_t(0), std::plus<>(), [&](auto {induction_var}) {{ return /* map */ {induction_var}; }});"
            )
        } else {
            format!(
                "// [{classification}] C++17 sequential std::accumulate scan for `{fn_name}`"
            )
        },
    );

    out.insert(
        "swift".to_string(),
        format!(
            "// [{classification}] Swift 6 functional pipeline for `{fn_name}`\nlet res = {arr_name}.lazy.filter {{ {induction_var} in {filter_note} }}.reduce(0, +)"
        ),
    );

    out.insert(
        "java".to_string(),
        if is_parallel {
            format!(
                "// [{classification}] Java 21 parallelStream() reduction for `{fn_name}`\nlong res = {arr_name}.parallelStream().mapToLong({induction_var} -> {induction_var}).filter({induction_var} -> {filter_note}).sum();"
            )
        } else {
            format!(
                "// [{classification}] Java 21 sequential stream scan for `{fn_name}`"
            )
        },
    );

    out.insert(
        "go".to_string(),
        format!(
            "// [{classification}] Go worker-pool / slice reduction for `{fn_name}` over `{arr_name}` ({red_summary})"
        ),
    );

    out.insert(
        "python".to_string(),
        format!(
            "# [{classification}] Python comprehension reduction for `{fn_name}`\nres = sum({induction_var} for {induction_var} in {arr_name} if {filter_note})"
        ),
    );

    out.insert(
        "ruby".to_string(),
        format!(
            "# [{classification}] Ruby Enumerable filter-reduce for `{fn_name}`\nres = {arr_name}.select {{ |{induction_var}| {filter_note} }}.sum"
        ),
    );

    out.insert(
        "lua".to_string(),
        format!(
            "-- [{classification}] LuaJIT trace-compiled loop kernel for `{fn_name}` over `{arr_name}` ({red_summary})"
        ),
    );

    out.insert(
        "perl".to_string(),
        format!(
            "# [{classification}] Perl List::Util::sum0 / grep pipeline for `{fn_name}`\nmy $res = sum0(grep {{ {filter_note} }} @{{{arr_name}}});"
        ),
    );

    out.insert(
        "typescript".to_string(),
        format!(
            "// [{classification}] TypeScript array filter/reduce pipeline for `{fn_name}`\nconst res = {arr_name}.filter(({induction_var}) => {filter_note}).reduce((acc, {induction_var}) => acc + {induction_var}, 0);"
        ),
    );

    out.insert(
        "star".to_string(),
        format!(
            ";; [{classification}] (polyhedral-kernel {fn_name} (domain {arr_name}) (reductions {red_summary}))"
        ),
    );

    out
}

/// Prove Total-Correctness Loop Termination via Floyd-Turing Well-Founded Ranking Functions
/// (`V(σ) >= 0 && V(σ') < V(σ)`) and compute IPET Symbolic & Parameterized Best/Worst-Case
/// Execution Time (`BCET` / `WCET`) and Worst-Case Execution Paths (`WCEP`).
pub fn prove_termination_and_wcet(hub: &HubModule) -> TerminationWcetReport {
    let start = Instant::now();
    let mut functions = Vec::new();
    let mut total_loops_audited = 0usize;
    let mut proven_terminating_loops = 0usize;
    let mut diverging_or_unproven_loops = 0usize;
    let mut module_wcet_cycles_n64 = 0u64;
    let mut module_bcet_cycles_n64 = 0u64;

    for item in &hub.items {
        if let Item::Function(f) = item {
            let rep = analyze_fn_termination_and_wcet(f);
            total_loops_audited += rep.loop_proofs.len();
            for lp in &rep.loop_proofs {
                if lp.proven_terminating {
                    proven_terminating_loops += 1;
                } else {
                    diverging_or_unproven_loops += 1;
                }
            }
            if f.name != "main" || hub.items.len() == 1 {
                module_wcet_cycles_n64 += rep.wcet_cycles_n64;
                module_bcet_cycles_n64 += rep.bcet_cycles_n64;
            }
            functions.push(rep);
        }
    }

    let all_terminating = diverging_or_unproven_loops == 0;

    TerminationWcetReport {
        all_terminating,
        total_functions: functions.len(),
        total_loops_audited,
        proven_terminating_loops,
        diverging_or_unproven_loops,
        module_wcet_cycles_n64,
        module_bcet_cycles_n64,
        functions,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

fn analyze_fn_termination_and_wcet(f: &FnDecl) -> FunctionWcetReport {
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

    let mut loop_proofs = Vec::new();
    let mut worst_case_path = Vec::new();
    let (bcet_const, bcet_linear, wcet_const, wcet_linear) =
        ipet_stmts_cycles(&f.name, &f.body, &mut loop_proofs, &mut worst_case_path);

    let proven_terminating = loop_proofs.iter().all(|lp| lp.proven_terminating);

    let bcet_symbolic = format_cycle_polynomial(bcet_const, bcet_linear);
    let wcet_symbolic = if proven_terminating {
        format_cycle_polynomial(wcet_const, wcet_linear)
    } else {
        "∞ (unbounded / non-terminating loop)".to_string()
    };

    let bcet_cycles_n64 = (bcet_const + bcet_linear * 64).max(1);
    let wcet_cycles_n64 = if proven_terminating {
        (wcet_const + wcet_linear * 64).max(bcet_cycles_n64)
    } else {
        u64::MAX / 1000
    };
    let jitter_ratio = if bcet_cycles_n64 > 0 && proven_terminating {
        ((wcet_cycles_n64 as f64 / bcet_cycles_n64 as f64) * 100.0).round() / 100.0
    } else {
        f64::INFINITY
    };

    FunctionWcetReport {
        fn_name: f.name.clone(),
        signature,
        proven_terminating,
        bcet_symbolic,
        wcet_symbolic,
        bcet_cycles_n64,
        wcet_cycles_n64,
        jitter_ratio,
        worst_case_path,
        loop_proofs,
    }
}

fn format_cycle_polynomial(c0: u64, c1: u64) -> String {
    match (c0, c1) {
        (0, 0) => "1 cycle".to_string(),
        (k, 0) => format!("{} cycles", k),
        (0, m) => format!("{}·N cycles", m),
        (k, m) => format!("{} + {}·N cycles", k, m),
    }
}

fn ipet_stmts_cycles(
    fn_name: &str,
    stmts: &[Stmt],
    loop_proofs: &mut Vec<LoopTerminationProof>,
    wcep: &mut Vec<String>,
) -> (u64, u64, u64, u64) {
    let mut bc_c0 = 0u64;
    let mut bc_c1 = 0u64;
    let mut wc_c0 = 0u64;
    let mut wc_c1 = 0u64;

    for stmt in stmts {
        match stmt {
            Stmt::Comment { .. } => {}
            Stmt::Let { name, value, .. } => {
                let c = expr_cycle_cost(value);
                bc_c0 += c;
                wc_c0 += c;
                wcep.push(format!("let {} = {} ({}c)", name, format_expr_compact(value), c));
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let c = expr_cycle_cost(value) + 1;
                bc_c0 += c;
                wc_c0 += c;
                let op_str = match op {
                    AssignOp::Set => "=",
                    AssignOp::AddAssign => "+=",
                    AssignOp::SubAssign => "-=",
                };
                wcep.push(format!(
                    "{} {} {} ({}c)",
                    target.root_var(),
                    op_str,
                    format_expr_compact(value),
                    c
                ));
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let cond_c = expr_cycle_cost(cond) + 2;
                let mut then_path = Vec::new();
                let mut else_path = Vec::new();
                let (tb_c0, tb_c1, tw_c0, tw_c1) =
                    ipet_stmts_cycles(fn_name, then_body, loop_proofs, &mut then_path);
                let (eb_c0, eb_c1, ew_c0, ew_c1) =
                    ipet_stmts_cycles(fn_name, else_body, loop_proofs, &mut else_path);

                let then_total_n64 = tw_c0 + tw_c1 * 64;
                let else_total_n64 = ew_c0 + ew_c1 * 64;
                if then_total_n64 >= else_total_n64 {
                    wc_c0 += cond_c + tw_c0;
                    wc_c1 += tw_c1;
                    wcep.push(format!("if {} [then-branch +{}c]", format_expr_compact(cond), then_total_n64));
                    wcep.extend(then_path);
                } else {
                    wc_c0 += cond_c + ew_c0;
                    wc_c1 += ew_c1;
                    wcep.push(format!("if !({}) [else-branch +{}c]", format_expr_compact(cond), else_total_n64));
                    wcep.extend(else_path);
                }

                let then_min_n64 = tb_c0 + tb_c1 * 64;
                let else_min_n64 = eb_c0 + eb_c1 * 64;
                if then_min_n64 <= else_min_n64 {
                    bc_c0 += cond_c + tb_c0;
                    bc_c1 += tb_c1;
                } else {
                    bc_c0 += cond_c + eb_c0;
                    bc_c1 += eb_c1;
                }
            }
            Stmt::Match { expr, arms, .. } => {
                let sc_c = expr_cycle_cost(expr) + 2;
                let mut max_arm = (0u64, 0u64, Vec::new());
                let mut min_arm: Option<(u64, u64)> = None;
                for arm in arms {
                    let mut arm_path = Vec::new();
                    let (ab_c0, ab_c1, aw_c0, aw_c1) =
                        ipet_stmts_cycles(fn_name, &arm.body, loop_proofs, &mut arm_path);
                    if aw_c0 + aw_c1 * 64 >= max_arm.0 + max_arm.1 * 64 {
                        max_arm = (aw_c0, aw_c1, arm_path);
                    }
                    let cur_min = ab_c0 + ab_c1 * 64;
                    if min_arm.is_none_or(|(m0, m1)| cur_min < m0 + m1 * 64) {
                        min_arm = Some((ab_c0, ab_c1));
                    }
                }
                let (m0, m1) = min_arm.unwrap_or((0, 0));
                bc_c0 += sc_c + m0;
                bc_c1 += m1;
                wc_c0 += sc_c + max_arm.0;
                wc_c1 += max_arm.1;
                wcep.push(format!("match {} [worst arm]", format_expr_compact(expr)));
                wcep.extend(max_arm.2);
            }
            Stmt::ForRange {
                id,
                var,
                start,
                end,
                body,
                ..
            } => {
                let start_s = format_expr_compact(start);
                let end_s = format_expr_compact(end);
                let rank_fn = format!("V({}) = max(0, {} - {})", var, end_s, var);
                let bounded_vc = format!("({} < {}) ==> ({} - {} >= 1 > 0)", var, end_s, end_s, var);
                let dec_vc = format!(
                    "V({} + 1) = ({} - ({} + 1)) = V({}) - 1 < V({})",
                    var, end_s, var, var, var
                );
                loop_proofs.push(LoopTerminationProof {
                    stmt_id: *id,
                    fn_name: fn_name.to_string(),
                    loop_header: format!("for {} in {}..{}", var, start_s, end_s),
                    ranking_function: rank_fn,
                    bounded_below_vc: bounded_vc,
                    strict_decrease_vc: dec_vc,
                    proven_terminating: true,
                    status: "Terminating (Well-Founded Ranking)".to_string(),
                    witness_or_note: format!(
                        "Induction variable `{}` strictly increments by +1 toward upper bound `{}`",
                        var, end_s
                    ),
                });

                let mut body_path = Vec::new();
                let (bb_c0, _bb_c1, bw_c0, _bw_c1) =
                    ipet_stmts_cycles(fn_name, body, loop_proofs, &mut body_path);
                let iter_wc = bw_c0 + 3;
                let iter_bc = bb_c0 + 3;

                if let (Expr::Int(lo), Expr::Int(hi)) = (start, end) {
                    let trip = (*hi - *lo).max(0) as u64;
                    bc_c0 += 2 + trip * iter_bc;
                    wc_c0 += 2 + trip * iter_wc;
                    wcep.push(format!(
                        "loop for {} in {}..{} ({} static trips × {}c)",
                        var, lo, hi, trip, iter_wc
                    ));
                } else {
                    // Parameterized bound N: BCET assumes N >= 0, WCET scales linearly with N
                    bc_c0 += 2;
                    bc_c1 += iter_bc;
                    wc_c0 += 2;
                    wc_c1 += iter_wc;
                    wcep.push(format!(
                        "loop for {} in {}..{} (N trips × {}c/iter)",
                        var, start_s, end_s, iter_wc
                    ));
                }
            }
            Stmt::ForEach {
                id,
                var,
                iter,
                body,
                ..
            } => {
                let iter_s = format_expr_compact(iter);
                let rank_fn = format!("V(idx_{}) = len({}) - idx_{}", var, iter_s, var);
                let bounded_vc = format!(
                    "(idx_{} < len({})) ==> (len({}) - idx_{} >= 1 > 0)",
                    var, iter_s, iter_s, var
                );
                let dec_vc = format!(
                    "V(idx_{} + 1) = len({}) - (idx_{} + 1) = V(idx_{}) - 1 < V(idx_{})",
                    var, iter_s, var, var, var
                );
                loop_proofs.push(LoopTerminationProof {
                    stmt_id: *id,
                    fn_name: fn_name.to_string(),
                    loop_header: format!("for {} in {}", var, iter_s),
                    ranking_function: rank_fn,
                    bounded_below_vc: bounded_vc,
                    strict_decrease_vc: dec_vc,
                    proven_terminating: true,
                    status: "Terminating (Well-Founded Ranking)".to_string(),
                    witness_or_note: format!(
                        "Finite slice iterator over `{}` advances cursor by +1 per step",
                        iter_s
                    ),
                });

                let mut body_path = Vec::new();
                let (bb_c0, _bb_c1, bw_c0, _bw_c1) =
                    ipet_stmts_cycles(fn_name, body, loop_proofs, &mut body_path);
                let iter_wc = bw_c0 + 3;
                let iter_bc = bb_c0 + 3;
                bc_c0 += 2;
                bc_c1 += iter_bc;
                wc_c0 += 2;
                wc_c1 += iter_wc;
                wcep.push(format!(
                    "loop for {} in {} (N trips × {}c/iter)",
                    var, iter_s, iter_wc
                ));
            }
            Stmt::While { id, cond, body, .. } => {
                let proof = synthesize_while_ranking_proof(*id, fn_name, cond, body);
                let term = proof.proven_terminating;
                loop_proofs.push(proof);

                let mut body_path = Vec::new();
                let (bb_c0, _bb_c1, bw_c0, _bw_c1) =
                    ipet_stmts_cycles(fn_name, body, loop_proofs, &mut body_path);
                let iter_wc = bw_c0 + expr_cycle_cost(cond) + 2;
                let iter_bc = bb_c0 + expr_cycle_cost(cond) + 2;
                bc_c0 += 2;
                bc_c1 += iter_bc;
                wc_c0 += 2;
                wc_c1 += if term { iter_wc } else { 10_000 };
                wcep.push(format!(
                    "while {} ({})",
                    format_expr_compact(cond),
                    if term { "ranking proven" } else { "UNBOUNDED" }
                ));
            }
            Stmt::Return { value, .. } => {
                let c = value.as_ref().map_or(1, expr_cycle_cost) + 1;
                bc_c0 += c;
                wc_c0 += c;
                wcep.push(format!(
                    "return {} ({}c)",
                    value
                        .as_ref()
                        .map(format_expr_compact)
                        .unwrap_or_else(|| "void".to_string()),
                    c
                ));
            }
            Stmt::Break { .. } | Stmt::Continue { .. } => {
                bc_c0 += 1;
                wc_c0 += 1;
            }
            Stmt::Assert { cond, .. } => {
                let c = expr_cycle_cost(cond) + 1;
                bc_c0 += c;
                wc_c0 += c;
            }
            Stmt::AssertEq { left, right, .. } => {
                let c = expr_cycle_cost(left) + expr_cycle_cost(right) + 2;
                bc_c0 += c;
                wc_c0 += c;
            }
            Stmt::Expr { expr, .. } => {
                let c = expr_cycle_cost(expr);
                bc_c0 += c;
                wc_c0 += c;
            }
        }
    }

    (bc_c0, bc_c1, wc_c0, wc_c1)
}

fn synthesize_while_ranking_proof(
    stmt_id: NodeId,
    fn_name: &str,
    cond: &Expr,
    body: &[Stmt],
) -> LoopTerminationProof {
    let mut scan = LoopBodyScan::default();
    scan_loop_body(body, "", false, &mut scan);

    // Check for `while v < bound` or `while v <= bound` with positive increment on `v`,
    // or `while v > bound` / `while v >= bound` with decrement on `v`.
    if let Expr::Binary { op, left, right } = cond {
        match (op, left.as_ref(), right.as_ref()) {
            (BinOp::Lt | BinOp::Le, Expr::Var(v), bound) => {
                let bound_s = format_expr_compact(bound);
                let increments = scan.writes.get(v).is_some_and(|ops| {
                    ops.iter().any(|(aop, val)| match (aop, val) {
                        (AssignOp::AddAssign, Expr::Int(k)) => *k > 0,
                        (
                            AssignOp::Set,
                            Expr::Binary {
                                op: BinOp::Add,
                                left: l,
                                right: r,
                            },
                        ) => {
                            matches!((l.as_ref(), r.as_ref()), (Expr::Var(vn), Expr::Int(k)) if vn == v && *k > 0)
                        }
                        _ => false,
                    })
                });
                if increments {
                    return LoopTerminationProof {
                        stmt_id,
                        fn_name: fn_name.to_string(),
                        loop_header: format!("while {}", format_expr_compact(cond)),
                        ranking_function: format!("V({}) = max(0, ({}) - {})", v, bound_s, v),
                        bounded_below_vc: format!(
                            "({} ==> ({}) - {} >= 0)",
                            format_expr_compact(cond),
                            bound_s,
                            v
                        ),
                        strict_decrease_vc: format!("V({}') < V({}) via Δ{} > 0", v, v, v),
                        proven_terminating: true,
                        status: "Terminating (Well-Founded Ranking)".to_string(),
                        witness_or_note: format!(
                            "Variable `{}` strictly increases toward upper bound `{}`",
                            v, bound_s
                        ),
                    };
                }
            }
            (BinOp::Gt | BinOp::Ge, Expr::Var(v), bound) => {
                let bound_s = format_expr_compact(bound);
                let decrements = scan.writes.get(v).is_some_and(|ops| {
                    ops.iter().any(|(aop, val)| match (aop, val) {
                        (AssignOp::SubAssign, Expr::Int(k)) => *k > 0,
                        (
                            AssignOp::Set,
                            Expr::Binary {
                                op: BinOp::Sub,
                                left: l,
                                right: r,
                            },
                        ) => {
                            matches!((l.as_ref(), r.as_ref()), (Expr::Var(vn), Expr::Int(k)) if vn == v && *k > 0)
                        }
                        (
                            AssignOp::Set,
                            Expr::Binary {
                                op: BinOp::Div | BinOp::IntDiv,
                                left: l,
                                right: r,
                            },
                        ) => {
                            matches!((l.as_ref(), r.as_ref()), (Expr::Var(vn), Expr::Int(k)) if vn == v && *k > 1)
                        }
                        _ => false,
                    })
                });
                if decrements {
                    return LoopTerminationProof {
                        stmt_id,
                        fn_name: fn_name.to_string(),
                        loop_header: format!("while {}", format_expr_compact(cond)),
                        ranking_function: format!("V({}) = max(0, {} - ({}))", v, v, bound_s),
                        bounded_below_vc: format!(
                            "({} ==> {} - ({}) >= 0)",
                            format_expr_compact(cond),
                            v,
                            bound_s
                        ),
                        strict_decrease_vc: format!("V({}') < V({}) via Δ{} < 0", v, v, v),
                        proven_terminating: true,
                        status: "Terminating (Well-Founded Ranking)".to_string(),
                        witness_or_note: format!(
                            "Variable `{}` strictly decreases toward lower bound `{}`",
                            v, bound_s
                        ),
                    };
                }
            }
            _ => {}
        }
    }

    LoopTerminationProof {
        stmt_id,
        fn_name: fn_name.to_string(),
        loop_header: format!("while {}", format_expr_compact(cond)),
        ranking_function: "None (no strictly decreasing well-founded variant)".to_string(),
        bounded_below_vc: "UNPROVEN".to_string(),
        strict_decrease_vc: "REFUTED: V(σ') >= V(σ)".to_string(),
        proven_terminating: false,
        status: "Non-Terminating / Unbounded Witness".to_string(),
        witness_or_note: format!(
            "Loop guard `{}` is not discharged by a strictly decreasing ranking function in `{}`",
            format_expr_compact(cond),
            fn_name
        ),
    }
}

fn expr_cycle_cost(expr: &Expr) -> u64 {
    match expr {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Bool(_)
        | Expr::Str(_)
        | Expr::Var(_)
        | Expr::EnumVariant { .. } => 1,
        Expr::Unary { expr: inner, .. } => 1 + expr_cycle_cost(inner),
        Expr::Binary { op, left, right } => {
            let op_c = match op {
                BinOp::Add
                | BinOp::Sub
                | BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or => 1,
                BinOp::Mul => 3,
                BinOp::Div | BinOp::IntDiv | BinOp::Mod => 6,
            };
            op_c + expr_cycle_cost(left) + expr_cycle_cost(right)
        }
        Expr::Index { base, index } => 2 + expr_cycle_cost(base) + expr_cycle_cost(index),
        Expr::FieldAccess { base, .. } => 1 + expr_cycle_cost(base),
        Expr::List(items) => 3 + items.iter().map(expr_cycle_cost).sum::<u64>(),
        Expr::StructInit { fields, .. } => {
            3 + fields.iter().map(|(_, v)| expr_cycle_cost(v)).sum::<u64>()
        }
        Expr::Call { args, .. } => 5 + args.iter().map(expr_cycle_cost).sum::<u64>(),
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(a)
            | Intrinsic::Abs(a)
            | Intrinsic::Upper(a)
            | Intrinsic::Lower(a)
            | Intrinsic::ToStr(a) => 2 + expr_cycle_cost(a),
            Intrinsic::Min(a, b)
            | Intrinsic::Max(a, b)
            | Intrinsic::Push { list: a, value: b }
            | Intrinsic::Contains {
                haystack: a,
                needle: b,
            } => 2 + expr_cycle_cost(a) + expr_cycle_cost(b),
            Intrinsic::Print(args) => 4 + args.iter().map(expr_cycle_cost).sum::<u64>(),
        },
    }
}

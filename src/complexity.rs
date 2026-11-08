use std::collections::{BTreeMap, HashMap, HashSet};

use crate::eval::{eval_fn_with_values, Value};
use crate::hub::{
    AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, NodeId, Stmt, Type,
};
use crate::lens::SpokeId;
use crate::spokes::lens_for;
use crate::wasm::compile_wasm;

const SCALING_SIZES: [usize; 5] = [4, 8, 16, 32, 64];
const MAX_PROFILE_STEPS: usize = 50_000;

#[derive(Debug, Clone)]
pub struct ScalingPoint {
    pub n: usize,
    pub steps: usize,
    pub compute_gas: u64,
    pub memory_gas: u64,
    pub alloc_gas: u64,
    pub branch_gas: u64,
    pub total_gas: u64,
}

#[derive(Debug, Clone)]
pub struct FunctionComplexity {
    pub name: String,
    pub signature: String,
    pub cyclomatic_complexity: usize,
    pub max_loop_depth: usize,
    pub is_recursive: bool,
    pub heap_alloc_sites: usize,
    pub static_big_o: String,
    pub empirical_big_o: String,
    pub growth_ratio: f64,
    pub scaling_points: Vec<ScalingPoint>,
}

#[derive(Debug, Clone, Default)]
pub struct ModuleGasBreakdown {
    pub total_steps: usize,
    pub compute_gas: u64,
    pub memory_gas: u64,
    pub alloc_gas: u64,
    pub branch_gas: u64,
    pub total_gas: u64,
}

#[derive(Debug, Clone)]
pub struct SpokeCodeMetrics {
    pub spoke: String,
    pub display_name: String,
    pub total_lines: usize,
    pub logic_lines: usize,
    pub bytes: usize,
    pub tokens: usize,
}

#[derive(Debug, Clone)]
pub struct ComplexityReport {
    pub total_functions: usize,
    pub max_cyclomatic: usize,
    pub max_loop_depth: usize,
    pub dominant_big_o: String,
    pub module_gas: ModuleGasBreakdown,
    pub functions: Vec<FunctionComplexity>,
    pub spoke_metrics: Vec<SpokeCodeMetrics>,
    pub wasm_bytes: usize,
}

pub fn analyze_complexity(hub: &HubModule) -> ComplexityReport {
    let call_graph = build_call_graph(hub);
    let seed_calls = collect_seed_call_args(hub);

    let mut stmt_gas_table: HashMap<NodeId, StmtGasCost> = HashMap::new();
    let mut numbered = hub.clone();
    assign_profile_ids(&mut numbered, &mut stmt_gas_table);

    let mut functions = Vec::new();
    let mut max_cyclomatic = 1usize;
    let mut max_loop_depth = 0usize;
    let mut dominant_rank = 0usize;
    let mut dominant_big_o = "O(1)".to_string();

    for item in &numbered.items {
        if let Item::Function(f) = item {
            let fc = analyze_single_fn(f, &numbered, &call_graph, &seed_calls, &stmt_gas_table);
            max_cyclomatic = max_cyclomatic.max(fc.cyclomatic_complexity);
            max_loop_depth = max_loop_depth.max(fc.max_loop_depth);
            let rank = big_o_rank(&fc.empirical_big_o).max(big_o_rank(&fc.static_big_o));
            if rank > dominant_rank {
                dominant_rank = rank;
                dominant_big_o = if big_o_rank(&fc.empirical_big_o) >= big_o_rank(&fc.static_big_o)
                {
                    fc.empirical_big_o.clone()
                } else {
                    fc.static_big_o.clone()
                };
            }
            functions.push(fc);
        }
    }

    let module_gas = profile_module_gas(&numbered, &stmt_gas_table);
    let spoke_metrics = compute_spoke_metrics(hub);
    let wasm_bytes = compile_wasm(hub).map(|w| w.bytes.len()).unwrap_or(0);

    ComplexityReport {
        total_functions: functions.len(),
        max_cyclomatic,
        max_loop_depth,
        dominant_big_o,
        module_gas,
        functions,
        spoke_metrics,
        wasm_bytes,
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct StmtGasCost {
    compute: u64,
    memory: u64,
    alloc: u64,
    branch: u64,
}

fn assign_profile_ids(hub: &mut HubModule, table: &mut HashMap<NodeId, StmtGasCost>) {
    let mut next_id: NodeId = 10_000;
    for item in &mut hub.items {
        match item {
            Item::Function(f) => number_and_cost_stmts(&mut f.body, &mut next_id, table),
            Item::Test(t) => number_and_cost_stmts(&mut t.body, &mut next_id, table),
            _ => {}
        }
    }
}

fn number_and_cost_stmts(
    stmts: &mut [Stmt],
    next_id: &mut NodeId,
    table: &mut HashMap<NodeId, StmtGasCost>,
) {
    for s in stmts {
        let id = *next_id;
        *next_id += 1;
        let mut cost = StmtGasCost::default();
        match s {
            Stmt::Comment { id: sid, .. } => {
                *sid = id;
            }
            Stmt::Let {
                id: sid, value, ..
            } => {
                *sid = id;
                cost.memory += 1;
                cost_expr(value, &mut cost);
            }
            Stmt::Assign {
                id: sid,
                target,
                value,
                ..
            } => {
                *sid = id;
                cost.memory += match target {
                    AssignTarget::Var(_) => 1,
                    AssignTarget::Field { .. } => 2,
                    AssignTarget::Index { index, .. } => {
                        cost_expr(index, &mut cost);
                        3
                    }
                };
                cost_expr(value, &mut cost);
            }
            Stmt::If {
                id: sid,
                cond,
                then_body,
                else_body,
                ..
            } => {
                *sid = id;
                cost.branch += 2;
                cost_expr(cond, &mut cost);
                number_and_cost_stmts(then_body, next_id, table);
                number_and_cost_stmts(else_body, next_id, table);
            }
            Stmt::Match {
                id: sid,
                expr,
                arms,
                ..
            } => {
                *sid = id;
                cost.branch += (arms.len() as u64).max(1) * 2;
                cost_expr(expr, &mut cost);
                for a in arms {
                    number_and_cost_stmts(&mut a.body, next_id, table);
                }
            }
            Stmt::While {
                id: sid,
                cond,
                body,
                ..
            } => {
                *sid = id;
                cost.branch += 2;
                cost_expr(cond, &mut cost);
                number_and_cost_stmts(body, next_id, table);
            }
            Stmt::ForEach {
                id: sid,
                iter,
                body,
                ..
            } => {
                *sid = id;
                cost.branch += 2;
                cost.memory += 2;
                cost_expr(iter, &mut cost);
                number_and_cost_stmts(body, next_id, table);
            }
            Stmt::ForRange {
                id: sid,
                start,
                end,
                body,
                ..
            } => {
                *sid = id;
                cost.branch += 2;
                cost.compute += 1;
                cost_expr(start, &mut cost);
                cost_expr(end, &mut cost);
                number_and_cost_stmts(body, next_id, table);
            }
            Stmt::Break { id: sid } | Stmt::Continue { id: sid } => {
                *sid = id;
                cost.branch += 1;
            }
            Stmt::Return { id: sid, value, .. } => {
                *sid = id;
                cost.branch += 1;
                if let Some(v) = value {
                    cost_expr(v, &mut cost);
                }
            }
            Stmt::Assert { id: sid, cond, .. } => {
                *sid = id;
                cost.branch += 1;
                cost_expr(cond, &mut cost);
            }
            Stmt::AssertEq {
                id: sid,
                left,
                right,
                ..
            } => {
                *sid = id;
                cost.branch += 1;
                cost.compute += 1;
                cost_expr(left, &mut cost);
                cost_expr(right, &mut cost);
            }
            Stmt::Expr { id: sid, expr, .. } => {
                *sid = id;
                cost_expr(expr, &mut cost);
            }
        }
        table.insert(id, cost);
    }
}

fn cost_expr(e: &Expr, cost: &mut StmtGasCost) {
    match e {
        Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::EnumVariant { .. } => {
            cost.compute += 1;
        }
        Expr::Str(s) => {
            cost.alloc += 2 + (s.len() as u64) / 8;
        }
        Expr::Var(_) => {
            cost.memory += 1;
        }
        Expr::List(items) => {
            cost.alloc += 4 + (items.len() as u64) * 2;
            for item in items {
                cost_expr(item, cost);
            }
        }
        Expr::StructInit { fields, .. } => {
            cost.alloc += 4 + (fields.len() as u64) * 2;
            for (_, v) in fields {
                cost_expr(v, cost);
            }
        }
        Expr::FieldAccess { base, .. } => {
            cost.memory += 2;
            cost_expr(base, cost);
        }
        Expr::Index { base, index } => {
            cost.memory += 3;
            cost_expr(base, cost);
            cost_expr(index, cost);
        }
        Expr::Unary { expr: inner, .. } => {
            cost.compute += 1;
            cost_expr(inner, cost);
        }
        Expr::Binary { op, left, right } => {
            match op {
                BinOp::And | BinOp::Or => cost.branch += 1,
                BinOp::Div | BinOp::IntDiv | BinOp::Mod => cost.compute += 3,
                BinOp::Mul => cost.compute += 2,
                _ => cost.compute += 1,
            }
            cost_expr(left, cost);
            cost_expr(right, cost);
        }
        Expr::Call { args, .. } => {
            cost.branch += 3;
            cost.memory += args.len() as u64;
            for a in args {
                cost_expr(a, cost);
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(a) => {
                cost.memory += 1;
                cost_expr(a, cost);
            }
            Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                cost.compute += 2;
                cost_expr(a, cost);
                cost_expr(b, cost);
            }
            Intrinsic::Abs(a) => {
                cost.compute += 1;
                cost_expr(a, cost);
            }
            Intrinsic::Upper(a) | Intrinsic::Lower(a) | Intrinsic::ToStr(a) => {
                cost.alloc += 4;
                cost.compute += 2;
                cost_expr(a, cost);
            }
            Intrinsic::Push { list, value } => {
                cost.alloc += 3;
                cost.memory += 2;
                cost_expr(list, cost);
                cost_expr(value, cost);
            }
            Intrinsic::Contains { haystack, needle } => {
                cost.memory += 4;
                cost.compute += 2;
                cost_expr(haystack, cost);
                cost_expr(needle, cost);
            }
            Intrinsic::Print(args) => {
                cost.compute += 2;
                for a in args {
                    cost_expr(a, cost);
                }
            }
        },
    }
}

struct GasObserver<'a> {
    table: &'a HashMap<NodeId, StmtGasCost>,
    steps: usize,
    compute_gas: u64,
    memory_gas: u64,
    alloc_gas: u64,
    branch_gas: u64,
}

impl<'a> crate::eval::VmObserver for GasObserver<'a> {
    fn on_stmt(&mut self, node_id: NodeId) {
        self.steps += 1;
        if let Some(c) = self.table.get(&node_id) {
            self.compute_gas += c.compute;
            self.memory_gas += c.memory;
            self.alloc_gas += c.alloc;
            self.branch_gas += c.branch;
        } else {
            self.compute_gas += 1;
        }
    }

    fn on_call_enter(&mut self, _depth: usize, _name: &str, args: &[Value]) -> Option<usize> {
        self.branch_gas += 2;
        self.memory_gas += args.len() as u64;
        None
    }

    fn on_call_exit(
        &mut self,
        _slot: Option<usize>,
        _name: &str,
        _ret: &Value,
        _steps_delta: usize,
    ) {
        self.branch_gas += 1;
    }
}

fn profile_module_gas(
    numbered: &HubModule,
    table: &HashMap<NodeId, StmtGasCost>,
) -> ModuleGasBreakdown {
    let mut obs = GasObserver {
        table,
        steps: 0,
        compute_gas: 0,
        memory_gas: 0,
        alloc_gas: 0,
        branch_gas: 0,
    };
    let _ = crate::eval::eval_with_observer(numbered, MAX_PROFILE_STEPS, &mut obs);
    let total_gas = obs.compute_gas + obs.memory_gas + obs.alloc_gas + obs.branch_gas;
    ModuleGasBreakdown {
        total_steps: obs.steps,
        compute_gas: obs.compute_gas,
        memory_gas: obs.memory_gas,
        alloc_gas: obs.alloc_gas,
        branch_gas: obs.branch_gas,
        total_gas,
    }
}

fn analyze_single_fn(
    f: &FnDecl,
    hub: &HubModule,
    call_graph: &HashMap<String, HashSet<String>>,
    seed_calls: &HashMap<String, Vec<Value>>,
    stmt_gas_table: &HashMap<NodeId, StmtGasCost>,
) -> FunctionComplexity {
    let params_str: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.ty.display()))
        .collect();
    let signature = format!("fn {}({}) -> {}", f.name, params_str.join(", "), f.ret_ty.display());

    let mut decision_points = 0usize;
    let mut max_loop_depth = 0usize;
    let mut heap_alloc_sites = 0usize;
    let mut direct_self_calls = 0usize;

    walk_stmts_metrics(
        &f.body,
        &f.name,
        0,
        call_graph,
        &mut decision_points,
        &mut max_loop_depth,
        &mut heap_alloc_sites,
        &mut direct_self_calls,
    );

    let is_recursive = is_fn_recursive(&f.name, call_graph);
    let cyclomatic_complexity = 1 + decision_points;

    let static_big_o = if is_recursive {
        if direct_self_calls >= 2 {
            "O(2^N)".to_string()
        } else if max_loop_depth >= 1 {
            "O(N^2)".to_string()
        } else {
            "O(N)".to_string()
        }
    } else {
        match max_loop_depth {
            0 => "O(1)".to_string(),
            1 => "O(N)".to_string(),
            2 => "O(N^2)".to_string(),
            3 => "O(N^3)".to_string(),
            d => format!("O(N^{})", d),
        }
    };

    let (scaling_points, growth_ratio, empirical_big_o) =
        profile_fn_scaling(f, hub, seed_calls, stmt_gas_table, &static_big_o);

    FunctionComplexity {
        name: f.name.clone(),
        signature,
        cyclomatic_complexity,
        max_loop_depth,
        is_recursive,
        heap_alloc_sites,
        static_big_o,
        empirical_big_o,
        growth_ratio,
        scaling_points,
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_stmts_metrics(
    stmts: &[Stmt],
    fn_name: &str,
    cur_loop_depth: usize,
    call_graph: &HashMap<String, HashSet<String>>,
    decision_points: &mut usize,
    max_loop_depth: &mut usize,
    heap_alloc_sites: &mut usize,
    direct_self_calls: &mut usize,
) {
    *max_loop_depth = (*max_loop_depth).max(cur_loop_depth);
    for s in stmts {
        match s {
            Stmt::Comment { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {}
            Stmt::Let { value, .. } => {
                walk_expr_metrics(
                    value,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Stmt::Assign { target, value, .. } => {
                if let crate::hub::AssignTarget::Index { index, .. } = target {
                    walk_expr_metrics(
                        index,
                        fn_name,
                        cur_loop_depth,
                        call_graph,
                        decision_points,
                        max_loop_depth,
                        heap_alloc_sites,
                        direct_self_calls,
                    );
                }
                walk_expr_metrics(
                    value,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                *decision_points += 1;
                walk_expr_metrics(
                    cond,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_stmts_metrics(
                    then_body,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_stmts_metrics(
                    else_body,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Stmt::Match { expr, arms, .. } => {
                *decision_points += arms.len().saturating_sub(1).max(1);
                walk_expr_metrics(
                    expr,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                for a in arms {
                    walk_stmts_metrics(
                        &a.body,
                        fn_name,
                        cur_loop_depth,
                        call_graph,
                        decision_points,
                        max_loop_depth,
                        heap_alloc_sites,
                        direct_self_calls,
                    );
                }
            }
            Stmt::While { cond, body, .. } => {
                *decision_points += 1;
                walk_expr_metrics(
                    cond,
                    fn_name,
                    cur_loop_depth + 1,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_stmts_metrics(
                    body,
                    fn_name,
                    cur_loop_depth + 1,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Stmt::ForEach { iter, body, .. } => {
                *decision_points += 1;
                walk_expr_metrics(
                    iter,
                    fn_name,
                    cur_loop_depth + 1,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_stmts_metrics(
                    body,
                    fn_name,
                    cur_loop_depth + 1,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Stmt::ForRange {
                start, end, body, ..
            } => {
                *decision_points += 1;
                walk_expr_metrics(
                    start,
                    fn_name,
                    cur_loop_depth + 1,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_expr_metrics(
                    end,
                    fn_name,
                    cur_loop_depth + 1,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_stmts_metrics(
                    body,
                    fn_name,
                    cur_loop_depth + 1,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Stmt::Return { value: Some(v), .. } | Stmt::Assert { cond: v, .. } | Stmt::Expr { expr: v, .. } => {
                walk_expr_metrics(
                    v,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Stmt::Return { value: None, .. } => {}
            Stmt::AssertEq { left, right, .. } => {
                walk_expr_metrics(
                    left,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_expr_metrics(
                    right,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_expr_metrics(
    e: &Expr,
    fn_name: &str,
    cur_loop_depth: usize,
    call_graph: &HashMap<String, HashSet<String>>,
    decision_points: &mut usize,
    max_loop_depth: &mut usize,
    heap_alloc_sites: &mut usize,
    direct_self_calls: &mut usize,
) {
    match e {
        Expr::List(items) => {
            *heap_alloc_sites += 1;
            for item in items {
                walk_expr_metrics(
                    item,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
        }
        Expr::StructInit { fields, .. } => {
            *heap_alloc_sites += 1;
            for (_, v) in fields {
                walk_expr_metrics(
                    v,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
        }
        Expr::FieldAccess { base, .. } | Expr::Unary { expr: base, .. } => {
            walk_expr_metrics(
                base,
                fn_name,
                cur_loop_depth,
                call_graph,
                decision_points,
                max_loop_depth,
                heap_alloc_sites,
                direct_self_calls,
            );
        }
        Expr::Index { base, index } => {
            walk_expr_metrics(
                base,
                fn_name,
                cur_loop_depth,
                call_graph,
                decision_points,
                max_loop_depth,
                heap_alloc_sites,
                direct_self_calls,
            );
            walk_expr_metrics(
                index,
                fn_name,
                cur_loop_depth,
                call_graph,
                decision_points,
                max_loop_depth,
                heap_alloc_sites,
                direct_self_calls,
            );
        }
        Expr::Binary { op, left, right } => {
            if matches!(op, BinOp::And | BinOp::Or) {
                *decision_points += 1;
            }
            walk_expr_metrics(
                left,
                fn_name,
                cur_loop_depth,
                call_graph,
                decision_points,
                max_loop_depth,
                heap_alloc_sites,
                direct_self_calls,
            );
            walk_expr_metrics(
                right,
                fn_name,
                cur_loop_depth,
                call_graph,
                decision_points,
                max_loop_depth,
                heap_alloc_sites,
                direct_self_calls,
            );
        }
        Expr::Call { func, args } => {
            if func == fn_name {
                *direct_self_calls += 1;
            }
            // If callee itself has loops, account for composed loop depth
            let _ = call_graph;
            for a in args {
                walk_expr_metrics(
                    a,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Push { list, value } => {
                *heap_alloc_sites += 1;
                walk_expr_metrics(
                    list,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_expr_metrics(
                    value,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Intrinsic::Contains { haystack, needle } => {
                // `contains` is an implicit inner linear scan over `haystack`
                *max_loop_depth = (*max_loop_depth).max(cur_loop_depth + 1);
                walk_expr_metrics(
                    haystack,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_expr_metrics(
                    needle,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Intrinsic::Upper(a) | Intrinsic::Lower(a) | Intrinsic::ToStr(a) => {
                *heap_alloc_sites += 1;
                walk_expr_metrics(
                    a,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Intrinsic::Len(a) | Intrinsic::Abs(a) => {
                walk_expr_metrics(
                    a,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                walk_expr_metrics(
                    a,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
                walk_expr_metrics(
                    b,
                    fn_name,
                    cur_loop_depth,
                    call_graph,
                    decision_points,
                    max_loop_depth,
                    heap_alloc_sites,
                    direct_self_calls,
                );
            }
            Intrinsic::Print(args) => {
                for a in args {
                    walk_expr_metrics(
                        a,
                        fn_name,
                        cur_loop_depth,
                        call_graph,
                        decision_points,
                        max_loop_depth,
                        heap_alloc_sites,
                        direct_self_calls,
                    );
                }
            }
        },
        _ => {}
    }
}

fn profile_fn_scaling(
    f: &FnDecl,
    hub: &HubModule,
    seed_calls: &HashMap<String, Vec<Value>>,
    stmt_gas_table: &HashMap<NodeId, StmtGasCost>,
    static_big_o: &str,
) -> (Vec<ScalingPoint>, f64, String) {
    let seed_args = seed_calls.get(&f.name);
    let has_list_param = f.params.iter().any(|p| matches!(p.ty, Type::List(_)));

    let mut points = Vec::with_capacity(SCALING_SIZES.len());
    for &n in &SCALING_SIZES {
        let args = build_scaled_args(f, hub, seed_args, n, has_list_param);
        if let Some(pt) = run_single_scaling_point(hub, &f.name, args, n, stmt_gas_table) {
            points.push(pt);
        }
    }

    if points.len() < 2 {
        return (points, 1.0, static_big_o.to_string());
    }

    // Compute growth ratio between N=16 -> N=32 and N=32 -> N=64
    let mut ratios = Vec::new();
    for pair in points.windows(2).skip(1) {
        let g1 = pair[0].total_gas.max(1) as f64;
        let g2 = pair[1].total_gas.max(1) as f64;
        ratios.push(g2 / g1);
    }
    let avg_ratio = if ratios.is_empty() {
        1.0
    } else {
        ratios.iter().sum::<f64>() / (ratios.len() as f64)
    };
    let rounded_ratio = (avg_ratio * 100.0).round() / 100.0;

    let empirical = if rounded_ratio < 1.25 {
        "O(1)".to_string()
    } else if rounded_ratio < 2.65 {
        "O(N)".to_string()
    } else if rounded_ratio < 5.50 {
        "O(N^2)".to_string()
    } else {
        "O(N^3 / 2^N)".to_string()
    };

    (points, rounded_ratio, empirical)
}

fn run_single_scaling_point(
    hub: &HubModule,
    fn_name: &str,
    args: Vec<Value>,
    n: usize,
    stmt_gas_table: &HashMap<NodeId, StmtGasCost>,
) -> Option<ScalingPoint> {
    let (_, _, steps) = eval_fn_with_values(hub, fn_name, args.clone(), MAX_PROFILE_STEPS).ok()?;
    // Estimate gas breakdown proportionally from function AST + executed step count
    let mut base_c = 0u64;
    let mut base_m = 0u64;
    let mut base_a = 0u64;
    let mut base_b = 0u64;
    if let Some(f) = hub.find_fn(fn_name) {
        sum_fn_stmt_weights(
            &f.body,
            stmt_gas_table,
            &mut base_c,
            &mut base_m,
            &mut base_a,
            &mut base_b,
        );
    }
    let weight_sum = (base_c + base_m + base_a + base_b).max(1);
    let total_units = (steps as u64).max(1) * 4;
    let compute_gas = ((total_units * base_c.max(1)) / weight_sum).max(1);
    let memory_gas = (total_units * base_m) / weight_sum + (args.len() as u64);
    let alloc_gas = (total_units * base_a) / weight_sum;
    let branch_gas = ((total_units * base_b) / weight_sum).max(1);
    let total_gas = compute_gas + memory_gas + alloc_gas + branch_gas;

    Some(ScalingPoint {
        n,
        steps,
        compute_gas,
        memory_gas,
        alloc_gas,
        branch_gas,
        total_gas,
    })
}

fn sum_fn_stmt_weights(
    stmts: &[Stmt],
    table: &HashMap<NodeId, StmtGasCost>,
    c: &mut u64,
    m: &mut u64,
    a: &mut u64,
    b: &mut u64,
) {
    for s in stmts {
        let sid = match s {
            Stmt::Comment { id, .. }
            | Stmt::Let { id, .. }
            | Stmt::Assign { id, .. }
            | Stmt::If { id, .. }
            | Stmt::Match { id, .. }
            | Stmt::While { id, .. }
            | Stmt::ForEach { id, .. }
            | Stmt::ForRange { id, .. }
            | Stmt::Break { id }
            | Stmt::Continue { id }
            | Stmt::Return { id, .. }
            | Stmt::Assert { id, .. }
            | Stmt::AssertEq { id, .. }
            | Stmt::Expr { id, .. } => *id,
        };
        if let Some(cost) = table.get(&sid) {
            *c += cost.compute;
            *m += cost.memory;
            *a += cost.alloc;
            *b += cost.branch;
        }
        match s {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                sum_fn_stmt_weights(then_body, table, c, m, a, b);
                sum_fn_stmt_weights(else_body, table, c, m, a, b);
            }
            Stmt::Match { arms, .. } => {
                for arm in arms {
                    sum_fn_stmt_weights(&arm.body, table, c, m, a, b);
                }
            }
            Stmt::While { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::ForRange { body, .. } => {
                sum_fn_stmt_weights(body, table, c, m, a, b);
            }
            _ => {}
        }
    }
}

fn build_scaled_args(
    f: &FnDecl,
    hub: &HubModule,
    seed_args: Option<&Vec<Value>>,
    n: usize,
    has_list_param: bool,
) -> Vec<Value> {
    let mut out = Vec::with_capacity(f.params.len());
    let mut scaled_int_done = false;

    for (idx, param) in f.params.iter().enumerate() {
        let seed_val = seed_args.and_then(|sa| sa.get(idx));
        match &param.ty {
            Type::List(elem_ty) => {
                let template: Vec<Value> = match seed_val {
                    Some(Value::List(items)) if !items.is_empty() => items.clone(),
                    _ => vec![
                        default_value_for_type(elem_ty, hub, 0),
                        default_value_for_type(elem_ty, hub, 1),
                        default_value_for_type(elem_ty, hub, 2),
                    ],
                };
                let mut list = Vec::with_capacity(n);
                for i in 0..n {
                    list.push(template[i % template.len()].clone());
                }
                out.push(Value::List(list));
            }
            Type::Int if !has_list_param && !scaled_int_done => {
                scaled_int_done = true;
                out.push(Value::Int(n as i64));
            }
            other => {
                if let Some(sv) = seed_val {
                    // If `sv` is a small window/budget parameter and we scale a list, make sure
                    // circuit-breaker budgets don't truncate early if it's a capacity/budget:
                    if let Value::Int(v) = sv {
                        if param.name.contains("budget")
                            || param.name.contains("capacity")
                            || param.name.contains("limit")
                        {
                            out.push(Value::Int((*v).max(10) * (n as i64)));
                            continue;
                        }
                    }
                    out.push(sv.clone());
                } else {
                    out.push(default_value_for_type(other, hub, idx));
                }
            }
        }
    }
    out
}

pub(crate) fn default_value_for_type(ty: &Type, hub: &HubModule, seed: usize) -> Value {
    match ty {
        Type::Int => Value::Int(10 + (seed as i64) * 5),
        Type::Float => Value::Float(10.0 + (seed as f64) * 2.5),
        Type::Bool => Value::Bool(seed.is_multiple_of(2)),
        Type::Str => Value::Str(format!("item_{}", seed)),
        Type::Void => Value::Void,
        Type::List(inner) => Value::List(vec![
            default_value_for_type(inner, hub, seed),
            default_value_for_type(inner, hub, seed + 1),
        ]),
        Type::Named(name) => {
            if let Some(en) = hub.find_enum(name) {
                let var = en
                    .variants
                    .get(seed % en.variants.len().max(1))
                    .cloned()
                    .unwrap_or_default();
                Value::EnumVariant {
                    enum_name: name.clone(),
                    variant: var,
                }
            } else if let Some(st) = hub.find_struct(name) {
                let mut fields = BTreeMap::new();
                for (i, fld) in st.fields.iter().enumerate() {
                    fields.insert(
                        fld.name.clone(),
                        default_value_for_type(&fld.ty, hub, seed + i),
                    );
                }
                Value::Struct {
                    name: name.clone(),
                    fields,
                }
            } else {
                Value::Int(1)
            }
        }
    }
}

struct SeedCallCollector {
    calls: HashMap<String, Vec<Value>>,
}

impl crate::eval::VmObserver for SeedCallCollector {
    fn on_stmt(&mut self, _node_id: NodeId) {}

    fn on_call_enter(&mut self, _depth: usize, name: &str, args: &[Value]) -> Option<usize> {
        self.calls
            .entry(name.to_string())
            .or_insert_with(|| args.to_vec());
        None
    }

    fn on_call_exit(
        &mut self,
        _slot: Option<usize>,
        _name: &str,
        _ret: &Value,
        _steps_delta: usize,
    ) {
    }
}

pub(crate) fn collect_seed_call_args(hub: &HubModule) -> HashMap<String, Vec<Value>> {
    let mut collector = SeedCallCollector {
        calls: HashMap::new(),
    };
    let _ = crate::eval::eval_with_observer(hub, MAX_PROFILE_STEPS, &mut collector);
    collector.calls
}

fn build_call_graph(hub: &HubModule) -> HashMap<String, HashSet<String>> {
    let mut graph: HashMap<String, HashSet<String>> = HashMap::new();
    for item in &hub.items {
        if let Item::Function(f) = item {
            let mut callees = HashSet::new();
            collect_callees_stmts(&f.body, &mut callees);
            graph.insert(f.name.clone(), callees);
        }
    }
    graph
}

fn collect_callees_stmts(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        match s {
            Stmt::Let { value, .. } | Stmt::Assign { value, .. } => {
                collect_callees_expr(value, out)
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                collect_callees_expr(cond, out);
                collect_callees_stmts(then_body, out);
                collect_callees_stmts(else_body, out);
            }
            Stmt::Match { expr, arms, .. } => {
                collect_callees_expr(expr, out);
                for a in arms {
                    collect_callees_stmts(&a.body, out);
                }
            }
            Stmt::While { cond, body, .. } => {
                collect_callees_expr(cond, out);
                collect_callees_stmts(body, out);
            }
            Stmt::ForEach { iter, body, .. } => {
                collect_callees_expr(iter, out);
                collect_callees_stmts(body, out);
            }
            Stmt::ForRange {
                start, end, body, ..
            } => {
                collect_callees_expr(start, out);
                collect_callees_expr(end, out);
                collect_callees_stmts(body, out);
            }
            Stmt::Return { value: Some(v), .. }
            | Stmt::Assert { cond: v, .. }
            | Stmt::Expr { expr: v, .. } => collect_callees_expr(v, out),
            Stmt::AssertEq { left, right, .. } => {
                collect_callees_expr(left, out);
                collect_callees_expr(right, out);
            }
            _ => {}
        }
    }
}

fn collect_callees_expr(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Call { func, args } => {
            out.insert(func.clone());
            for a in args {
                collect_callees_expr(a, out);
            }
        }
        Expr::List(items) => {
            for i in items {
                collect_callees_expr(i, out);
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, v) in fields {
                collect_callees_expr(v, out);
            }
        }
        Expr::FieldAccess { base, .. } | Expr::Unary { expr: base, .. } => {
            collect_callees_expr(base, out);
        }
        Expr::Index { base, index }
        | Expr::Binary {
            left: base,
            right: index,
            ..
        } => {
            collect_callees_expr(base, out);
            collect_callees_expr(index, out);
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(a)
            | Intrinsic::Abs(a)
            | Intrinsic::Upper(a)
            | Intrinsic::Lower(a)
            | Intrinsic::ToStr(a) => collect_callees_expr(a, out),
            Intrinsic::Min(a, b)
            | Intrinsic::Max(a, b)
            | Intrinsic::Push { list: a, value: b }
            | Intrinsic::Contains {
                haystack: a,
                needle: b,
            } => {
                collect_callees_expr(a, out);
                collect_callees_expr(b, out);
            }
            Intrinsic::Print(args) => {
                for a in args {
                    collect_callees_expr(a, out);
                }
            }
        },
        _ => {}
    }
}

fn is_fn_recursive(target: &str, graph: &HashMap<String, HashSet<String>>) -> bool {
    let mut visited = HashSet::new();
    let mut stack: Vec<String> = graph
        .get(target)
        .map(|s| s.iter().cloned().collect())
        .unwrap_or_default();
    while let Some(cur) = stack.pop() {
        if cur == target {
            return true;
        }
        if visited.insert(cur.clone()) {
            if let Some(next) = graph.get(&cur) {
                for n in next {
                    stack.push(n.clone());
                }
            }
        }
    }
    false
}

fn big_o_rank(label: &str) -> usize {
    if label.contains("2^N") || label.contains("N^3") {
        4
    } else if label.contains("N^2") {
        3
    } else if label.contains("O(N)") {
        2
    } else {
        1
    }
}

fn compute_spoke_metrics(hub: &HubModule) -> Vec<SpokeCodeMetrics> {
    let empty_hub = HubModule::new();
    let mut out = Vec::with_capacity(SpokeId::ALL.len());

    for spoke in SpokeId::ALL {
        let lens = lens_for(spoke);
        let full_src = lens.get(hub);
        let preamble_src = lens.get(&empty_hub);
        let preamble_non_empty = preamble_src
            .lines()
            .filter(|l| !l.trim().is_empty())
            .count();

        let total_lines = full_src.lines().filter(|l| !l.trim().is_empty()).count();
        let non_comment_lines = full_src
            .lines()
            .filter(|l| {
                let t = l.trim();
                !t.is_empty() && !t.starts_with("//") && !t.starts_with('#') && !t.starts_with("--")
            })
            .count();
        let logic_lines = non_comment_lines
            .saturating_sub(preamble_non_empty)
            .max(total_lines.saturating_sub(preamble_non_empty).min(non_comment_lines));
        let bytes = full_src.len();
        let tokens = full_src.split_whitespace().count();

        out.push(SpokeCodeMetrics {
            spoke: spoke.as_str().to_string(),
            display_name: spoke.display_name().to_string(),
            total_lines,
            logic_lines,
            bytes,
            tokens,
        });
    }

    out
}

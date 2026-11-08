use std::collections::{BTreeMap, HashSet};

use crate::eval::{eval_with_observer, Value, VmObserver};
use crate::hub::{AssignTarget, HubModule, Item, NodeId, Stmt};

const MAX_RECORDED_CALLS: usize = 64;
const DEFAULT_TRACE_STEP_BUDGET: usize = 50_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UncoveredStmt {
    pub node_id: NodeId,
    pub func: String,
    pub summary: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallTraceEntry {
    pub depth: usize,
    pub callee: String,
    pub args: String,
    pub result: String,
    pub steps: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnHotspot {
    pub name: String,
    pub calls: usize,
    pub total_steps: usize,
}

#[derive(Debug, Clone)]
pub struct TraceReport {
    pub ok: bool,
    pub coverage_pct: u8,
    pub covered_stmts: usize,
    pub total_stmts: usize,
    pub uncovered: Vec<UncoveredStmt>,
    pub hotspots: Vec<FnHotspot>,
    pub call_trace: Vec<CallTraceEntry>,
    pub error: Option<String>,
}

pub fn trace_module_default(hub: &HubModule) -> TraceReport {
    trace_module(hub, DEFAULT_TRACE_STEP_BUDGET)
}

pub fn trace_module(hub: &HubModule, max_steps: usize) -> TraceReport {
    let mut traced_hub = hub.clone();
    ensure_trace_stmt_ids(&mut traced_hub);

    let mut catalog: Vec<(NodeId, String, String)> = Vec::new();
    for item in &traced_hub.items {
        if let Item::Function(f) = item {
            collect_fn_stmts(&f.body, &f.name, &mut catalog);
        }
    }

    let mut collector = Collector {
        visited: HashSet::new(),
        call_counts: BTreeMap::new(),
        call_steps: BTreeMap::new(),
        active_depth: BTreeMap::new(),
        call_trace: Vec::new(),
    };

    let run_res = eval_with_observer(&traced_hub, max_steps, &mut collector);

    let total_stmts = catalog.len();
    let mut covered_stmts = 0usize;
    let mut uncovered = Vec::new();
    for (nid, fn_name, summary) in catalog {
        if collector.visited.contains(&nid) {
            covered_stmts += 1;
        } else {
            uncovered.push(UncoveredStmt {
                node_id: nid,
                func: fn_name,
                summary,
            });
        }
    }

    let coverage_pct = (covered_stmts * 100)
        .checked_div(total_stmts)
        .unwrap_or(100) as u8;

    let mut hotspots: Vec<FnHotspot> = collector
        .call_counts
        .into_iter()
        .map(|(name, calls)| {
            let total_steps = collector.call_steps.get(&name).copied().unwrap_or(0);
            FnHotspot {
                name,
                calls,
                total_steps,
            }
        })
        .collect();
    hotspots.sort_by(|a, b| b.total_steps.cmp(&a.total_steps).then(a.name.cmp(&b.name)));

    TraceReport {
        ok: run_res.is_ok(),
        coverage_pct,
        covered_stmts,
        total_stmts,
        uncovered,
        hotspots,
        call_trace: collector.call_trace,
        error: run_res.err(),
    }
}

struct Collector {
    visited: HashSet<NodeId>,
    call_counts: BTreeMap<String, usize>,
    call_steps: BTreeMap<String, usize>,
    active_depth: BTreeMap<String, usize>,
    call_trace: Vec<CallTraceEntry>,
}

impl VmObserver for Collector {
    fn on_stmt(&mut self, node_id: NodeId) {
        self.visited.insert(node_id);
    }

    fn on_call_enter(&mut self, depth: usize, name: &str, args: &[Value]) -> Option<usize> {
        *self.call_counts.entry(name.to_string()).or_insert(0) += 1;
        *self.active_depth.entry(name.to_string()).or_insert(0) += 1;
        if self.call_trace.len() < MAX_RECORDED_CALLS {
            let idx = self.call_trace.len();
            let args_str: Vec<String> = args.iter().map(compact_value).collect();
            self.call_trace.push(CallTraceEntry {
                depth,
                callee: name.to_string(),
                args: args_str.join(", "),
                result: "...".to_string(),
                steps: 0,
            });
            Some(idx)
        } else {
            None
        }
    }

    fn on_call_exit(&mut self, slot: Option<usize>, name: &str, ret: &Value, steps_delta: usize) {
        let active = self.active_depth.entry(name.to_string()).or_insert(1);
        *active = active.saturating_sub(1);
        // Record inclusive step cost at outermost call boundary for recursive-safe hotspot ranking
        if *active == 0 {
            *self.call_steps.entry(name.to_string()).or_insert(0) += steps_delta;
        }
        if let Some(idx) = slot {
            if let Some(entry) = self.call_trace.get_mut(idx) {
                entry.result = compact_value(ret);
                entry.steps = steps_delta;
            }
        }
    }
}

fn ensure_trace_stmt_ids(hub: &mut HubModule) {
    let mut max_id: NodeId = 0;
    for item in &hub.items {
        match item {
            Item::Function(f) => scan_max_stmt_id(&f.body, &mut max_id),
            Item::Test(t) => scan_max_stmt_id(&t.body, &mut max_id),
            _ => {}
        }
    }
    let mut next_id = max_id + 1;
    let mut seen = HashSet::new();
    for item in &mut hub.items {
        match item {
            Item::Function(f) => assign_unique_stmt_ids(&mut f.body, &mut seen, &mut next_id),
            Item::Test(t) => assign_unique_stmt_ids(&mut t.body, &mut seen, &mut next_id),
            _ => {}
        }
    }
}

fn scan_max_stmt_id(stmts: &[Stmt], max_id: &mut NodeId) {
    for stmt in stmts {
        match stmt {
            Stmt::Comment { id, .. }
            | Stmt::Let { id, .. }
            | Stmt::Assign { id, .. }
            | Stmt::Break { id }
            | Stmt::Continue { id }
            | Stmt::Return { id, .. }
            | Stmt::Assert { id, .. }
            | Stmt::AssertEq { id, .. }
            | Stmt::Expr { id, .. } => {
                *max_id = (*max_id).max(*id);
            }
            Stmt::If {
                id,
                then_body,
                else_body,
                ..
            } => {
                *max_id = (*max_id).max(*id);
                scan_max_stmt_id(then_body, max_id);
                scan_max_stmt_id(else_body, max_id);
            }
            Stmt::Match { id, arms, .. } => {
                *max_id = (*max_id).max(*id);
                for arm in arms {
                    scan_max_stmt_id(&arm.body, max_id);
                }
            }
            Stmt::While { id, body, .. }
            | Stmt::ForEach { id, body, .. }
            | Stmt::ForRange { id, body, .. } => {
                *max_id = (*max_id).max(*id);
                scan_max_stmt_id(body, max_id);
            }
        }
    }
}

fn assign_unique_stmt_ids(stmts: &mut [Stmt], seen: &mut HashSet<NodeId>, next_id: &mut NodeId) {
    for stmt in stmts {
        match stmt {
            Stmt::Comment { id, .. }
            | Stmt::Let { id, .. }
            | Stmt::Assign { id, .. }
            | Stmt::Break { id }
            | Stmt::Continue { id }
            | Stmt::Return { id, .. }
            | Stmt::Assert { id, .. }
            | Stmt::AssertEq { id, .. }
            | Stmt::Expr { id, .. } => {
                if *id == 0 || !seen.insert(*id) {
                    *id = *next_id;
                    *next_id += 1;
                    seen.insert(*id);
                }
            }
            Stmt::If {
                id,
                then_body,
                else_body,
                ..
            } => {
                if *id == 0 || !seen.insert(*id) {
                    *id = *next_id;
                    *next_id += 1;
                    seen.insert(*id);
                }
                assign_unique_stmt_ids(then_body, seen, next_id);
                assign_unique_stmt_ids(else_body, seen, next_id);
            }
            Stmt::Match { id, arms, .. } => {
                if *id == 0 || !seen.insert(*id) {
                    *id = *next_id;
                    *next_id += 1;
                    seen.insert(*id);
                }
                for arm in arms {
                    assign_unique_stmt_ids(&mut arm.body, seen, next_id);
                }
            }
            Stmt::While { id, body, .. }
            | Stmt::ForEach { id, body, .. }
            | Stmt::ForRange { id, body, .. } => {
                if *id == 0 || !seen.insert(*id) {
                    *id = *next_id;
                    *next_id += 1;
                    seen.insert(*id);
                }
                assign_unique_stmt_ids(body, seen, next_id);
            }
        }
    }
}

fn compact_value(v: &Value) -> String {
    let s = v.display_str();
    if s.chars().count() > 48 {
        let prefix: String = s.chars().take(45).collect();
        format!("{}...", prefix)
    } else {
        s
    }
}

fn collect_fn_stmts(stmts: &[Stmt], fn_name: &str, out: &mut Vec<(NodeId, String, String)>) {
    for stmt in stmts {
        match stmt {
            Stmt::Comment { .. } => {}
            Stmt::Let { id, name, .. } => {
                out.push((*id, fn_name.to_string(), format!("let {}", name)));
            }
            Stmt::Assign { id, target, .. } => {
                let tgt = match target {
                    AssignTarget::Var(v) => v.clone(),
                    AssignTarget::Field { base, field } => format!("{}.{}", base, field),
                    AssignTarget::Index { base, .. } => format!("{}[..]", base),
                };
                out.push((*id, fn_name.to_string(), format!("assign {}", tgt)));
            }
            Stmt::If {
                id,
                then_body,
                else_body,
                ..
            } => {
                out.push((*id, fn_name.to_string(), "if branch".to_string()));
                collect_fn_stmts(then_body, fn_name, out);
                collect_fn_stmts(else_body, fn_name, out);
            }
            Stmt::Match { id, arms, .. } => {
                out.push((*id, fn_name.to_string(), "match/switch".to_string()));
                for arm in arms {
                    collect_fn_stmts(&arm.body, fn_name, out);
                }
            }
            Stmt::While { id, body, .. } => {
                out.push((*id, fn_name.to_string(), "while loop".to_string()));
                collect_fn_stmts(body, fn_name, out);
            }
            Stmt::ForEach { id, var, body, .. } => {
                out.push((*id, fn_name.to_string(), format!("for-each {}", var)));
                collect_fn_stmts(body, fn_name, out);
            }
            Stmt::ForRange { id, var, body, .. } => {
                out.push((*id, fn_name.to_string(), format!("for-range {}", var)));
                collect_fn_stmts(body, fn_name, out);
            }
            Stmt::Break { id } => {
                out.push((*id, fn_name.to_string(), "break".to_string()));
            }
            Stmt::Continue { id } => {
                out.push((*id, fn_name.to_string(), "continue".to_string()));
            }
            Stmt::Return { id, .. } => {
                out.push((*id, fn_name.to_string(), "return".to_string()));
            }
            Stmt::Assert { id, .. } => {
                out.push((*id, fn_name.to_string(), "assert".to_string()));
            }
            Stmt::AssertEq { id, .. } => {
                out.push((*id, fn_name.to_string(), "assert_eq".to_string()));
            }
            Stmt::Expr { id, .. } => {
                out.push((*id, fn_name.to_string(), "expr stmt".to_string()));
            }
        }
    }
}

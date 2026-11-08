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
    let mut catalog: Vec<(NodeId, String, String)> = Vec::new();
    for item in &hub.items {
        if let Item::Function(f) = item {
            collect_fn_stmts(&f.body, &f.name, &mut catalog);
        }
    }

    let mut collector = Collector {
        visited: HashSet::new(),
        call_counts: BTreeMap::new(),
        call_steps: BTreeMap::new(),
        call_trace: Vec::new(),
    };

    let run_res = eval_with_observer(hub, max_steps, &mut collector);

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
    call_trace: Vec<CallTraceEntry>,
}

impl VmObserver for Collector {
    fn on_stmt(&mut self, node_id: NodeId) {
        self.visited.insert(node_id);
    }

    fn on_call_enter(&mut self, depth: usize, name: &str, args: &[Value]) -> Option<usize> {
        *self.call_counts.entry(name.to_string()).or_insert(0) += 1;
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
        // Record inclusive step cost for top-level / leaf hotspot ranking
        *self.call_steps.entry(name.to_string()).or_insert(0) += steps_delta;
        if let Some(idx) = slot {
            if let Some(entry) = self.call_trace.get_mut(idx) {
                entry.result = compact_value(ret);
                entry.steps = steps_delta;
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

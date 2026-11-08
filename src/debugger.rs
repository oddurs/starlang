use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::eval::Value;
use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, MatchPat, NodeId,
    Stmt, UnaryOp,
};
use crate::lens::SpokeId;
use crate::spokes::lens_for;

const DEFAULT_DEBUG_MAX_STEPS: usize = 512;
const MAX_DEBUG_CALL_DEPTH: usize = 64;

#[derive(Debug, Clone)]
pub struct VarDelta {
    pub name: String,
    pub before: Option<String>,
    pub after: String,
}

#[derive(Debug, Clone)]
pub struct TimeTravelStep {
    pub step_index: usize,
    pub stmt_id: NodeId,
    pub func: String,
    pub depth: usize,
    pub kind: String,
    pub summary: String,
    pub deltas: Vec<VarDelta>,
    pub locals: BTreeMap<String, String>,
    pub call_stack: Vec<String>,
    pub stdout_so_far: String,
    pub spoke_lines: BTreeMap<String, usize>,
    pub read_vars: Vec<String>,
    pub written_var: Option<String>,
    pub control_parent_step: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct BackwardSlice {
    pub target: String,
    pub anchor_step: usize,
    pub slice_steps: Vec<usize>,
    pub explanation: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct TimeTravelReport {
    pub ok: bool,
    pub fault: Option<String>,
    pub total_steps: usize,
    pub max_depth: usize,
    pub final_stdout: String,
    pub steps: Vec<TimeTravelStep>,
    pub stmt_spoke_lines: BTreeMap<NodeId, BTreeMap<String, usize>>,
    pub slice: Option<BackwardSlice>,
}

pub fn record_time_travel_default(
    hub: &HubModule,
    slice_target: Option<&str>,
) -> TimeTravelReport {
    record_time_travel(hub, slice_target, DEFAULT_DEBUG_MAX_STEPS)
}

pub fn record_time_travel(
    hub: &HubModule,
    slice_target: Option<&str>,
    max_steps: usize,
) -> TimeTravelReport {
    let mut numbered_hub = hub.clone();
    ensure_stmt_node_ids(&mut numbered_hub);

    let stmt_spoke_lines = compute_stmt_spoke_lines(&numbered_hub);
    let mut fns = HashMap::new();
    for item in &numbered_hub.items {
        if let Item::Function(f) = item {
            fns.insert(f.name.clone(), f);
        }
    }

    let mut recorder = Recorder {
        fns: &fns,
        stmt_spoke_lines: &stmt_spoke_lines,
        steps: Vec::new(),
        stdout: String::new(),
        call_stack: Vec::new(),
        ctrl_stack: Vec::new(),
        max_steps,
        max_depth: 0,
    };

    let mut ok = true;
    let mut fault = None;

    if numbered_hub.has_main() {
        if let Err(err) = recorder.call_fn("main", Vec::new(), None) {
            ok = false;
            fault = Some(err);
        }
    } else {
        for item in &numbered_hub.items {
            if let Item::Test(t) = item {
                if let Err(err) = recorder.run_test_body(&t.name, &t.body) {
                    ok = false;
                    fault = Some(err);
                    break;
                }
            }
        }
    }

    let slice = if let Some(t) = slice_target.map(str::trim).filter(|s| !s.is_empty()) {
        compute_backward_slice(&recorder.steps, t)
    } else if !ok && !recorder.steps.is_empty() {
        compute_backward_slice(&recorder.steps, "fault")
    } else if !recorder.steps.is_empty() {
        // Default slice: anchor on the last mutated or returned variable in the trace
        let default_target = recorder
            .steps
            .iter()
            .rev()
            .find_map(|s| s.written_var.clone())
            .unwrap_or_else(|| format!("step:{}", recorder.steps.len() - 1));
        compute_backward_slice(&recorder.steps, &default_target)
    } else {
        None
    };

    TimeTravelReport {
        ok,
        fault,
        total_steps: recorder.steps.len(),
        max_depth: recorder.max_depth,
        final_stdout: recorder.stdout,
        steps: recorder.steps,
        stmt_spoke_lines,
        slice,
    }
}

/// Compute the exact 1-based line number of every `Stmt` (`NodeId`) across all 13 spoke languages
/// by injecting single-line probe comments into a temporary clone of `hub` and stripping them while
/// counting real lines.
pub fn compute_stmt_spoke_lines(
    hub: &HubModule,
) -> BTreeMap<NodeId, BTreeMap<String, usize>> {
    let mut probe_hub = hub.clone();
    for item in &mut probe_hub.items {
        match item {
            Item::Function(f) => inject_line_probes(&mut f.body),
            Item::Test(t) => inject_line_probes(&mut t.body),
            _ => {}
        }
    }

    let mut out: BTreeMap<NodeId, BTreeMap<String, usize>> = BTreeMap::new();
    for spoke in SpokeId::ALL {
        let lens = lens_for(spoke);
        let projected = lens.get(&probe_hub);
        let spoke_key = spoke.as_str().to_string();

        let mut real_line = 1usize;
        let mut pending_probes: Vec<NodeId> = Vec::new();

        for raw_line in projected.lines() {
            if let Some(pos) = raw_line.find("__STAR_PROBE_") {
                let after = &raw_line[pos + "__STAR_PROBE_".len()..];
                if let Some(end) = after.find("__") {
                    if let Ok(id) = after[..end].parse::<NodeId>() {
                        pending_probes.push(id);
                    }
                }
                continue;
            }

            let trimmed = raw_line.trim();
            let is_type_doc_prefix = trimmed.starts_with("---@type")
                || trimmed.starts_with("# @type")
                || trimmed.starts_with("# @star-");

            if !pending_probes.is_empty() && !is_type_doc_prefix {
                for id in pending_probes.drain(..) {
                    out.entry(id).or_default().insert(spoke_key.clone(), real_line);
                }
            }
            real_line += 1;
        }
    }

    out
}

fn stmt_node_id(s: &Stmt) -> NodeId {
    match s {
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
    }
}

fn ensure_stmt_node_ids(hub: &mut HubModule) {
    fn number_stmts(stmts: &mut [Stmt], next_id: &mut NodeId) {
        for s in stmts {
            match s {
                Stmt::Comment { id, .. }
                | Stmt::Let { id, .. }
                | Stmt::Assign { id, .. }
                | Stmt::Break { id }
                | Stmt::Continue { id }
                | Stmt::Return { id, .. }
                | Stmt::Assert { id, .. }
                | Stmt::AssertEq { id, .. }
                | Stmt::Expr { id, .. } => {
                    if *id == 0 {
                        *id = *next_id;
                        *next_id += 1;
                    }
                }
                Stmt::If {
                    id,
                    then_body,
                    else_body,
                    ..
                } => {
                    if *id == 0 {
                        *id = *next_id;
                        *next_id += 1;
                    }
                    number_stmts(then_body, next_id);
                    number_stmts(else_body, next_id);
                }
                Stmt::Match { id, arms, .. } => {
                    if *id == 0 {
                        *id = *next_id;
                        *next_id += 1;
                    }
                    for a in arms {
                        number_stmts(&mut a.body, next_id);
                    }
                }
                Stmt::While { id, body, .. }
                | Stmt::ForEach { id, body, .. }
                | Stmt::ForRange { id, body, .. } => {
                    if *id == 0 {
                        *id = *next_id;
                        *next_id += 1;
                    }
                    number_stmts(body, next_id);
                }
            }
        }
    }

    let mut next_id = hub.next_id.max(1000);
    for item in &mut hub.items {
        match item {
            Item::Function(f) => number_stmts(&mut f.body, &mut next_id),
            Item::Test(t) => number_stmts(&mut t.body, &mut next_id),
            _ => {}
        }
    }
}

fn inject_line_probes(stmts: &mut Vec<Stmt>) {
    let old = std::mem::take(stmts);
    let mut next = Vec::with_capacity(old.len() * 2);
    for mut s in old {
        let sid = stmt_node_id(&s);
        match &mut s {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                inject_line_probes(then_body);
                inject_line_probes(else_body);
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    inject_line_probes(&mut a.body);
                }
            }
            Stmt::While { body, .. }
            | Stmt::ForRange { body, .. }
            | Stmt::ForEach { body, .. } => {
                inject_line_probes(body);
            }
            _ => {}
        }
        if sid != 0 && !matches!(s, Stmt::Comment { .. }) {
            next.push(Stmt::Comment {
                id: 0,
                text: format!("__STAR_PROBE_{}__", sid),
            });
        }
        next.push(s);
    }
    *stmts = next;
}

/// Compute a dynamic backward program slice (data + control dependencies) from `target`.
/// `target` can be `"step:<idx>"`, `"fault"`, `"<fn>::<var>"`, or a bare variable name `"<var>"`.
pub fn compute_backward_slice(
    steps: &[TimeTravelStep],
    target: &str,
) -> Option<BackwardSlice> {
    if steps.is_empty() {
        return None;
    }

    let t = target.trim();
    let (anchor_step, resolved_label) = if t.eq_ignore_ascii_case("fault") {
        let idx = steps.len() - 1;
        (idx, format!("step:{} ({})", idx, steps[idx].kind))
    } else if let Some(rest) = t.strip_prefix("step:") {
        let idx = rest.trim().parse::<usize>().ok()?.min(steps.len() - 1);
        (idx, format!("step:{}", idx))
    } else if t.contains("::") {
        let idx = steps
            .iter()
            .rposition(|s| {
                s.written_var.as_deref() == Some(t) || s.read_vars.iter().any(|r| r == t)
            })?;
        (idx, t.to_string())
    } else {
        let suffix = format!("::{}", t);
        let idx = steps.iter().rposition(|s| {
            s.written_var
                .as_ref()
                .is_some_and(|w| w.ends_with(&suffix))
                || s.read_vars.iter().any(|r| r.ends_with(&suffix))
        })?;
        let full_var = steps[idx]
            .written_var
            .clone()
            .filter(|w| w.ends_with(&suffix))
            .or_else(|| {
                steps[idx]
                    .read_vars
                    .iter()
                    .find(|r| r.ends_with(&suffix))
                    .cloned()
            })
            .unwrap_or_else(|| t.to_string());
        (idx, full_var)
    };

    let mut in_slice: BTreeSet<usize> = BTreeSet::new();
    let mut needed_vars: BTreeSet<String> = BTreeSet::new();
    in_slice.insert(anchor_step);

    for r in &steps[anchor_step].read_vars {
        needed_vars.insert(r.clone());
    }
    if let Some(ctrl) = steps[anchor_step].control_parent_step {
        in_slice.insert(ctrl);
    }

    for idx in (0..anchor_step).rev() {
        let step = &steps[idx];
        let mut matched = in_slice.contains(&idx);
        if let Some(w) = &step.written_var {
            if needed_vars.contains(w) {
                matched = true;
                needed_vars.remove(w);
            }
        }
        if matched {
            in_slice.insert(idx);
            for r in &step.read_vars {
                needed_vars.insert(r.clone());
            }
            if let Some(ctrl) = step.control_parent_step {
                in_slice.insert(ctrl);
            }
        }
    }

    let slice_steps: Vec<usize> = in_slice.into_iter().collect();
    let mut explanation = Vec::new();
    for &idx in &slice_steps {
        let st = &steps[idx];
        let rs_line = st.spoke_lines.get("rust").copied().unwrap_or(0);
        let pl_line = st.spoke_lines.get("perl").copied().unwrap_or(0);
        let lua_line = st.spoke_lines.get("lua").copied().unwrap_or(0);
        let py_line = st.spoke_lines.get("python").copied().unwrap_or(0);
        explanation.push(format!(
            "[Step {}] {}() :: {} (rs:L{}, py:L{}, lua:L{}, pl:L{})",
            idx, st.func, st.summary, rs_line, py_line, lua_line, pl_line
        ));
    }

    Some(BackwardSlice {
        target: resolved_label,
        anchor_step,
        slice_steps,
        explanation,
    })
}

enum DebugFlow {
    Next,
    Break,
    Continue,
    Return(Value),
}

struct Recorder<'a> {
    fns: &'a HashMap<String, &'a FnDecl>,
    stmt_spoke_lines: &'a BTreeMap<NodeId, BTreeMap<String, usize>>,
    steps: Vec<TimeTravelStep>,
    stdout: String,
    call_stack: Vec<String>,
    ctrl_stack: Vec<usize>,
    max_steps: usize,
    max_depth: usize,
}

impl<'a> Recorder<'a> {
    fn run_test_body(&mut self, test_name: &str, body: &[Stmt]) -> Result<(), String> {
        let fn_label = format!("test_{}", test_name);
        self.call_stack.push(fn_label.clone());
        self.max_depth = self.max_depth.max(self.call_stack.len());
        let mut env = BTreeMap::new();
        let res = self.exec_block(&fn_label, body, &mut env);
        self.call_stack.pop();
        res.map(|_| ())
    }

    fn call_fn(
        &mut self,
        name: &str,
        args: Vec<(Option<String>, Value)>,
        call_ctrl: Option<usize>,
    ) -> Result<Value, String> {
        if self.call_stack.len() >= MAX_DEBUG_CALL_DEPTH {
            return Err(format!("call stack depth exceeded in '{}'", name));
        }
        let f = self
            .fns
            .get(name)
            .ok_or_else(|| format!("unknown function '{}'", name))?;
        let mut env: BTreeMap<String, Value> = BTreeMap::new();
        for (param, (_, val)) in f.params.iter().zip(args) {
            env.insert(param.name.clone(), val);
        }

        self.call_stack.push(name.to_string());
        self.max_depth = self.max_depth.max(self.call_stack.len());
        if let Some(c) = call_ctrl {
            self.ctrl_stack.push(c);
        }
        let res = self.exec_block(name, &f.body, &mut env);
        if call_ctrl.is_some() {
            self.ctrl_stack.pop();
        }
        self.call_stack.pop();

        match res? {
            DebugFlow::Return(v) => Ok(v),
            _ => Ok(Value::Void),
        }
    }

    fn exec_block(
        &mut self,
        fn_name: &str,
        stmts: &[Stmt],
        env: &mut BTreeMap<String, Value>,
    ) -> Result<DebugFlow, String> {
        let mut block_lets: Vec<(String, Option<Value>)> = Vec::new();
        let mut out_flow = DebugFlow::Next;
        let mut err_out: Option<String> = None;
        for stmt in stmts {
            match stmt {
                Stmt::Let { name, .. }
                | Stmt::ForRange { var: name, .. }
                | Stmt::ForEach { var: name, .. } => {
                    block_lets.push((name.clone(), env.get(name).cloned()));
                }
                _ => {}
            }
            match self.exec_stmt(fn_name, stmt, env) {
                Ok(flow) => {
                    if !matches!(flow, DebugFlow::Next) {
                        out_flow = flow;
                        break;
                    }
                }
                Err(e) => {
                    err_out = Some(e);
                    break;
                }
            }
        }
        for (name, prev) in block_lets.into_iter().rev() {
            match prev {
                Some(v) => {
                    env.insert(name, v);
                }
                None => {
                    env.remove(&name);
                }
            }
        }
        if let Some(e) = err_out {
            Err(e)
        } else {
            Ok(out_flow)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn record_step(
        &mut self,
        stmt_id: NodeId,
        fn_name: &str,
        kind: &str,
        summary: String,
        deltas: Vec<VarDelta>,
        env: &BTreeMap<String, Value>,
        read_vars: Vec<String>,
        written_var: Option<String>,
    ) -> Result<usize, String> {
        if self.steps.len() >= self.max_steps {
            return Err(format!(
                "time-travel step budget ({}) reached",
                self.max_steps
            ));
        }
        let idx = self.steps.len();
        let locals: BTreeMap<String, String> = env
            .iter()
            .map(|(k, v)| (k.clone(), v.display_str()))
            .collect();
        let spoke_lines = self
            .stmt_spoke_lines
            .get(&stmt_id)
            .cloned()
            .unwrap_or_default();
        let control_parent_step = self.ctrl_stack.last().copied();

        self.steps.push(TimeTravelStep {
            step_index: idx,
            stmt_id,
            func: fn_name.to_string(),
            depth: self.call_stack.len(),
            kind: kind.to_string(),
            summary,
            deltas,
            locals,
            call_stack: self.call_stack.clone(),
            stdout_so_far: self.stdout.clone(),
            spoke_lines,
            read_vars,
            written_var,
            control_parent_step,
        });
        Ok(idx)
    }

    fn exec_stmt(
        &mut self,
        fn_name: &str,
        stmt: &Stmt,
        env: &mut BTreeMap<String, Value>,
    ) -> Result<DebugFlow, String> {
        let sid = stmt_node_id(stmt);
        match stmt {
            Stmt::Comment { .. } => Ok(DebugFlow::Next),
            Stmt::Let { name, value, .. } => {
                let mut reads = Vec::new();
                collect_expr_reads(value, fn_name, &mut reads);
                let val = self.eval_expr(fn_name, value, env)?;
                let after = val.display_str();
                let before = env.insert(name.clone(), val).map(|v| v.display_str());
                let delta = VarDelta {
                    name: name.clone(),
                    before,
                    after: after.clone(),
                };
                self.record_step(
                    sid,
                    fn_name,
                    "let",
                    format!("let {} = {}", name, after),
                    vec![delta],
                    env,
                    reads,
                    Some(format!("{}::{}", fn_name, name)),
                )?;
                Ok(DebugFlow::Next)
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let mut reads = Vec::new();
                collect_expr_reads(value, fn_name, &mut reads);
                let rhs = self.eval_expr(fn_name, value, env)?;
                let base_var = match target {
                    AssignTarget::Var(v) => v.clone(),
                    AssignTarget::Field { base, .. } => base.clone(),
                    AssignTarget::Index { base, index } => {
                        collect_expr_reads(index, fn_name, &mut reads);
                        base.clone()
                    }
                };
                if !matches!(op, AssignOp::Set) || !matches!(target, AssignTarget::Var(_)) {
                    let scoped = format!("{}::{}", fn_name, base_var);
                    if !reads.contains(&scoped) {
                        reads.push(scoped);
                    }
                }
                let before = env.get(&base_var).map(|v| v.display_str());
                self.apply_assign(fn_name, target, *op, rhs, env)?;
                let after = env
                    .get(&base_var)
                    .map(|v| v.display_str())
                    .unwrap_or_default();
                let summary = match &before {
                    Some(b) => format!("{} = {} -> {}", base_var, b, after),
                    None => format!("{} = {}", base_var, after),
                };
                let delta = VarDelta {
                    name: base_var.clone(),
                    before,
                    after,
                };
                self.record_step(
                    sid,
                    fn_name,
                    "assign",
                    summary,
                    vec![delta],
                    env,
                    reads,
                    Some(format!("{}::{}", fn_name, base_var)),
                )?;
                Ok(DebugFlow::Next)
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let mut reads = Vec::new();
                collect_expr_reads(cond, fn_name, &mut reads);
                let cval = self.eval_expr(fn_name, cond, env)?;
                let truth = matches!(cval, Value::Bool(true));
                let step_idx = self.record_step(
                    sid,
                    fn_name,
                    "if",
                    format!("if => {}", truth),
                    Vec::new(),
                    env,
                    reads,
                    None,
                )?;
                self.ctrl_stack.push(step_idx);
                let res = if truth {
                    self.exec_block(fn_name, then_body, env)
                } else {
                    self.exec_block(fn_name, else_body, env)
                };
                self.ctrl_stack.pop();
                res
            }
            Stmt::Match { expr, arms, .. } => {
                let mut reads = Vec::new();
                collect_expr_reads(expr, fn_name, &mut reads);
                let scrut = self.eval_expr(fn_name, expr, env)?;
                let step_idx = self.record_step(
                    sid,
                    fn_name,
                    "match",
                    format!("match {}", scrut.display_str()),
                    Vec::new(),
                    env,
                    reads,
                    None,
                )?;
                self.ctrl_stack.push(step_idx);
                let mut flow = DebugFlow::Next;
                for arm in arms {
                    if pat_matches(&arm.pat, &scrut) {
                        flow = self.exec_block(fn_name, &arm.body, env)?;
                        break;
                    }
                }
                self.ctrl_stack.pop();
                Ok(flow)
            }
            Stmt::While { cond, body, .. } => {
                loop {
                    let mut reads = Vec::new();
                    collect_expr_reads(cond, fn_name, &mut reads);
                    let cval = self.eval_expr(fn_name, cond, env)?;
                    let truth = matches!(cval, Value::Bool(true));
                    let step_idx = self.record_step(
                        sid,
                        fn_name,
                        "while",
                        format!("while => {}", truth),
                        Vec::new(),
                        env,
                        reads,
                        None,
                    )?;
                    if !truth {
                        break;
                    }
                    self.ctrl_stack.push(step_idx);
                    let flow = self.exec_block(fn_name, body, env)?;
                    self.ctrl_stack.pop();
                    match flow {
                        DebugFlow::Next | DebugFlow::Continue => {}
                        DebugFlow::Break => break,
                        DebugFlow::Return(v) => return Ok(DebugFlow::Return(v)),
                    }
                }
                Ok(DebugFlow::Next)
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                let mut reads = Vec::new();
                collect_expr_reads(start, fn_name, &mut reads);
                collect_expr_reads(end, fn_name, &mut reads);
                let lo = match self.eval_expr(fn_name, start, env)? {
                    Value::Int(v) => v,
                    _ => return Err("range start must be Int".to_string()),
                };
                let hi = match self.eval_expr(fn_name, end, env)? {
                    Value::Int(v) => v,
                    _ => return Err("range end must be Int".to_string()),
                };
                for idx_val in lo..hi {
                    let before = env.insert(var.clone(), Value::Int(idx_val)).map(|v| v.display_str());
                    let delta = VarDelta {
                        name: var.clone(),
                        before,
                        after: idx_val.to_string(),
                    };
                    let step_idx = self.record_step(
                        sid,
                        fn_name,
                        "for_range",
                        format!("for {} = {} (in {}..{})", var, idx_val, lo, hi),
                        vec![delta],
                        env,
                        reads.clone(),
                        Some(format!("{}::{}", fn_name, var)),
                    )?;
                    self.ctrl_stack.push(step_idx);
                    let flow = self.exec_block(fn_name, body, env)?;
                    self.ctrl_stack.pop();
                    match flow {
                        DebugFlow::Next | DebugFlow::Continue => {}
                        DebugFlow::Break => break,
                        DebugFlow::Return(v) => return Ok(DebugFlow::Return(v)),
                    }
                }
                Ok(DebugFlow::Next)
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let mut reads = Vec::new();
                collect_expr_reads(iter, fn_name, &mut reads);
                let items = match self.eval_expr(fn_name, iter, env)? {
                    Value::List(xs) => xs,
                    _ => return Err("for-each target must be a List".to_string()),
                };
                for item in items {
                    let after = item.display_str();
                    let before = env.insert(var.clone(), item).map(|v| v.display_str());
                    let delta = VarDelta {
                        name: var.clone(),
                        before,
                        after: after.clone(),
                    };
                    let step_idx = self.record_step(
                        sid,
                        fn_name,
                        "for_each",
                        format!("for {} = {}", var, after),
                        vec![delta],
                        env,
                        reads.clone(),
                        Some(format!("{}::{}", fn_name, var)),
                    )?;
                    self.ctrl_stack.push(step_idx);
                    let flow = self.exec_block(fn_name, body, env)?;
                    self.ctrl_stack.pop();
                    match flow {
                        DebugFlow::Next | DebugFlow::Continue => {}
                        DebugFlow::Break => break,
                        DebugFlow::Return(v) => return Ok(DebugFlow::Return(v)),
                    }
                }
                Ok(DebugFlow::Next)
            }
            Stmt::Return { value, .. } => {
                let mut reads = Vec::new();
                let val = if let Some(e) = value {
                    collect_expr_reads(e, fn_name, &mut reads);
                    self.eval_expr(fn_name, e, env)?
                } else {
                    Value::Void
                };
                self.record_step(
                    sid,
                    fn_name,
                    "return",
                    format!("return {}", val.display_str()),
                    Vec::new(),
                    env,
                    reads,
                    None,
                )?;
                Ok(DebugFlow::Return(val))
            }
            Stmt::Break { .. } => {
                self.record_step(
                    sid,
                    fn_name,
                    "break",
                    "break".to_string(),
                    Vec::new(),
                    env,
                    Vec::new(),
                    None,
                )?;
                Ok(DebugFlow::Break)
            }
            Stmt::Continue { .. } => {
                self.record_step(
                    sid,
                    fn_name,
                    "continue",
                    "continue".to_string(),
                    Vec::new(),
                    env,
                    Vec::new(),
                    None,
                )?;
                Ok(DebugFlow::Continue)
            }
            Stmt::Assert { cond, .. } => {
                let mut reads = Vec::new();
                collect_expr_reads(cond, fn_name, &mut reads);
                let v = self.eval_expr(fn_name, cond, env)?;
                let ok = matches!(v, Value::Bool(true));
                self.record_step(
                    sid,
                    fn_name,
                    if ok { "assert" } else { "fault" },
                    format!("assert => {}", ok),
                    Vec::new(),
                    env,
                    reads,
                    None,
                )?;
                if !ok {
                    return Err("assertion failed".to_string());
                }
                Ok(DebugFlow::Next)
            }
            Stmt::AssertEq { left, right, .. } => {
                let mut reads = Vec::new();
                collect_expr_reads(left, fn_name, &mut reads);
                collect_expr_reads(right, fn_name, &mut reads);
                let lv = self.eval_expr(fn_name, left, env)?;
                let rv = self.eval_expr(fn_name, right, env)?;
                let ok = lv == rv;
                self.record_step(
                    sid,
                    fn_name,
                    if ok { "assert" } else { "fault" },
                    format!("assert_eq({}, {}) => {}", lv.display_str(), rv.display_str(), ok),
                    Vec::new(),
                    env,
                    reads,
                    None,
                )?;
                if !ok {
                    return Err(format!(
                        "assert_eq failed: {} != {}",
                        lv.display_str(),
                        rv.display_str()
                    ));
                }
                Ok(DebugFlow::Next)
            }
            Stmt::Expr { expr, .. } => {
                let mut reads = Vec::new();
                collect_expr_reads(expr, fn_name, &mut reads);
                let written = if let Expr::Intrinsic(intr) = expr {
                    if let Intrinsic::Push {
                        list: Expr::Var(v), ..
                    } = intr.as_ref()
                    {
                        Some(v.clone())
                    } else {
                        None
                    }
                } else {
                    None
                };
                let before = written
                    .as_ref()
                    .and_then(|v| env.get(v).map(|val| val.display_str()));
                let _ = self.eval_expr(fn_name, expr, env)?;
                let mut deltas = Vec::new();
                let summary = if let Some(ref vname) = written {
                    let after = env
                        .get(vname)
                        .map(|val| val.display_str())
                        .unwrap_or_default();
                    deltas.push(VarDelta {
                        name: vname.clone(),
                        before,
                        after: after.clone(),
                    });
                    format!("push({}) -> {}", vname, after)
                } else if matches!(expr, Expr::Intrinsic(i) if matches!(i.as_ref(), Intrinsic::Print(_))) {
                    let last_line = self.stdout.lines().last().unwrap_or("");
                    format!("print(\"{}\")", last_line)
                } else {
                    "expr".to_string()
                };
                self.record_step(
                    sid,
                    fn_name,
                    "expr",
                    summary,
                    deltas,
                    env,
                    reads,
                    written.map(|v| format!("{}::{}", fn_name, v)),
                )?;
                Ok(DebugFlow::Next)
            }
        }
    }

    fn apply_assign(
        &mut self,
        fn_name: &str,
        target: &AssignTarget,
        op: AssignOp,
        rhs: Value,
        env: &mut BTreeMap<String, Value>,
    ) -> Result<(), String> {
        match target {
            AssignTarget::Var(name) => {
                let cur = env
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("undefined variable '{}'", name))?;
                let next = combine_assign(cur, op, rhs)?;
                env.insert(name.clone(), next);
                Ok(())
            }
            AssignTarget::Field { base, field } => {
                let cur = env
                    .get(base)
                    .cloned()
                    .ok_or_else(|| format!("undefined struct variable '{}'", base))?;
                if let Value::Struct { name, mut fields } = cur {
                    let fcur = fields
                        .get(field)
                        .cloned()
                        .ok_or_else(|| format!("unknown field '{}'", field))?;
                    let fnext = combine_assign(fcur, op, rhs)?;
                    fields.insert(field.clone(), fnext);
                    env.insert(base.clone(), Value::Struct { name, fields });
                    Ok(())
                } else {
                    Err(format!("'{}' is not a struct", base))
                }
            }
            AssignTarget::Index { base, index } => {
                let idx_val = match self.eval_expr(fn_name, index, env)? {
                    Value::Int(i) => i,
                    _ => return Err("list index must be Int".to_string()),
                };
                let cur = env
                    .get(base)
                    .cloned()
                    .ok_or_else(|| format!("undefined list variable '{}'", base))?;
                if let Value::List(mut items) = cur {
                    if idx_val < 0 || (idx_val as usize) >= items.len() {
                        return Err(format!("index {} out of bounds", idx_val));
                    }
                    let u = idx_val as usize;
                    items[u] = combine_assign(items[u].clone(), op, rhs)?;
                    env.insert(base.clone(), Value::List(items));
                    Ok(())
                } else {
                    Err(format!("'{}' is not a list", base))
                }
            }
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    fn eval_expr(
        &mut self,
        fn_name: &str,
        expr: &Expr,
        env: &mut BTreeMap<String, Value>,
    ) -> Result<Value, String> {
        match expr {
            Expr::Int(v) => Ok(Value::Int(*v)),
            Expr::Float(v) => Ok(Value::Float(*v)),
            Expr::Bool(b) => Ok(Value::Bool(*b)),
            Expr::Str(s) => Ok(Value::Str(s.clone())),
            Expr::Var(name) => env
                .get(name)
                .cloned()
                .ok_or_else(|| format!("undefined variable '{}'", name)),
            Expr::EnumVariant { enum_name, variant } => Ok(Value::EnumVariant {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
            }),
            Expr::List(items) => {
                let mut out = Vec::with_capacity(items.len());
                for it in items {
                    out.push(self.eval_expr(fn_name, it, env)?);
                }
                Ok(Value::List(out))
            }
            Expr::StructInit { name, fields } => {
                let mut map = BTreeMap::new();
                for (k, v) in fields {
                    map.insert(k.clone(), self.eval_expr(fn_name, v, env)?);
                }
                Ok(Value::Struct {
                    name: name.clone(),
                    fields: map,
                })
            }
            Expr::FieldAccess { base, field } => {
                let b = self.eval_expr(fn_name, base, env)?;
                if let Value::Struct { fields, .. } = b {
                    fields
                        .get(field)
                        .cloned()
                        .ok_or_else(|| format!("missing field '{}'", field))
                } else {
                    Err("field access on non-struct".to_string())
                }
            }
            Expr::Index { base, index } => {
                let b = self.eval_expr(fn_name, base, env)?;
                let i = match self.eval_expr(fn_name, index, env)? {
                    Value::Int(v) => v,
                    _ => return Err("index must be Int".to_string()),
                };
                if let Value::List(items) = b {
                    if i < 0 || (i as usize) >= items.len() {
                        return Err(format!("list index {} out of bounds (len={})", i, items.len()));
                    }
                    Ok(items[i as usize].clone())
                } else {
                    Err("indexing non-list".to_string())
                }
            }
            Expr::Unary { op, expr: inner } => {
                let v = self.eval_expr(fn_name, inner, env)?;
                match (op, v) {
                    (UnaryOp::Neg, Value::Int(i)) => Ok(Value::Int(i.wrapping_neg())),
                    (UnaryOp::Neg, Value::Float(f)) => Ok(Value::Float(-f)),
                    (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
                    _ => Err("invalid unary operand".to_string()),
                }
            }
            Expr::Binary { op, left, right } => {
                if *op == BinOp::And {
                    let l = self.eval_expr(fn_name, left, env)?;
                    if l == Value::Bool(false) {
                        return Ok(Value::Bool(false));
                    }
                    return self.eval_expr(fn_name, right, env);
                }
                if *op == BinOp::Or {
                    let l = self.eval_expr(fn_name, left, env)?;
                    if l == Value::Bool(true) {
                        return Ok(Value::Bool(true));
                    }
                    return self.eval_expr(fn_name, right, env);
                }
                let lv = self.eval_expr(fn_name, left, env)?;
                let rv = self.eval_expr(fn_name, right, env)?;
                eval_binop(*op, lv, rv)
            }
            Expr::Call { func, args } => {
                let mut evaluated = Vec::with_capacity(args.len());
                for a in args {
                    evaluated.push((None, self.eval_expr(fn_name, a, env)?));
                }
                let ctrl = self.ctrl_stack.last().copied();
                self.call_fn(func, evaluated, ctrl)
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(x) => match self.eval_expr(fn_name, x, env)? {
                    Value::List(xs) => Ok(Value::Int(xs.len() as i64)),
                    Value::Str(s) => Ok(Value::Int(s.len() as i64)),
                    _ => Err("len requires List or Str".to_string()),
                },
                Intrinsic::Push { list, value } => {
                    let val = self.eval_expr(fn_name, value, env)?;
                    if let Expr::Var(vname) = list {
                        let cur = env
                            .get(vname)
                            .cloned()
                            .ok_or_else(|| format!("undefined list '{}'", vname))?;
                        if let Value::List(mut items) = cur {
                            items.push(val);
                            env.insert(vname.clone(), Value::List(items));
                            Ok(Value::Void)
                        } else {
                            Err("push target is not a List".to_string())
                        }
                    } else {
                        Err("push requires list variable".to_string())
                    }
                }
                Intrinsic::Min(a, b) => {
                    let va = self.eval_expr(fn_name, a, env)?;
                    let vb = self.eval_expr(fn_name, b, env)?;
                    match (va, vb) {
                        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x.min(y))),
                        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x.min(y))),
                        _ => Err("min requires numeric args".to_string()),
                    }
                }
                Intrinsic::Max(a, b) => {
                    let va = self.eval_expr(fn_name, a, env)?;
                    let vb = self.eval_expr(fn_name, b, env)?;
                    match (va, vb) {
                        (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x.max(y))),
                        (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x.max(y))),
                        _ => Err("max requires numeric args".to_string()),
                    }
                }
                Intrinsic::Abs(a) => match self.eval_expr(fn_name, a, env)? {
                    Value::Int(x) => Ok(Value::Int(x.wrapping_abs())),
                    Value::Float(x) => Ok(Value::Float(x.abs())),
                    _ => Err("abs requires numeric arg".to_string()),
                },
                Intrinsic::Upper(a) => match self.eval_expr(fn_name, a, env)? {
                    Value::Str(s) => Ok(Value::Str(s.to_uppercase())),
                    _ => Err("upper requires Str".to_string()),
                },
                Intrinsic::Lower(a) => match self.eval_expr(fn_name, a, env)? {
                    Value::Str(s) => Ok(Value::Str(s.to_lowercase())),
                    _ => Err("lower requires Str".to_string()),
                },
                Intrinsic::ToStr(a) => {
                    let v = self.eval_expr(fn_name, a, env)?;
                    Ok(Value::Str(v.display_str()))
                }
                Intrinsic::Contains { haystack, needle } => {
                    let h = self.eval_expr(fn_name, haystack, env)?;
                    let n = self.eval_expr(fn_name, needle, env)?;
                    match (h, n) {
                        (Value::Str(hs), Value::Str(ns)) => Ok(Value::Bool(hs.contains(&ns))),
                        (Value::List(items), needle_val) => {
                            Ok(Value::Bool(items.contains(&needle_val)))
                        }
                        _ => Err("contains type mismatch".to_string()),
                    }
                }
                Intrinsic::Print(args) => {
                    let mut parts = Vec::with_capacity(args.len());
                    for a in args {
                        parts.push(self.eval_expr(fn_name, a, env)?.display_str());
                    }
                    self.stdout.push_str(&parts.join(" "));
                    self.stdout.push('\n');
                    Ok(Value::Void)
                }
            },
        }
    }
}

fn collect_expr_reads(expr: &Expr, fn_name: &str, out: &mut Vec<String>) {
    match expr {
        Expr::Var(v) => {
            let scoped = format!("{}::{}", fn_name, v);
            if !out.contains(&scoped) {
                out.push(scoped);
            }
        }
        Expr::List(items) => {
            for it in items {
                collect_expr_reads(it, fn_name, out);
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, v) in fields {
                collect_expr_reads(v, fn_name, out);
            }
        }
        Expr::FieldAccess { base, .. } | Expr::Unary { expr: base, .. } => {
            collect_expr_reads(base, fn_name, out);
        }
        Expr::Index { base, index } => {
            collect_expr_reads(base, fn_name, out);
            collect_expr_reads(index, fn_name, out);
        }
        Expr::Binary { left, right, .. } => {
            collect_expr_reads(left, fn_name, out);
            collect_expr_reads(right, fn_name, out);
        }
        Expr::Call { args, .. } => {
            for a in args {
                collect_expr_reads(a, fn_name, out);
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(a)
            | Intrinsic::Abs(a)
            | Intrinsic::Upper(a)
            | Intrinsic::Lower(a)
            | Intrinsic::ToStr(a) => collect_expr_reads(a, fn_name, out),
            Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                collect_expr_reads(a, fn_name, out);
                collect_expr_reads(b, fn_name, out);
            }
            Intrinsic::Push { list, value } => {
                collect_expr_reads(list, fn_name, out);
                collect_expr_reads(value, fn_name, out);
            }
            Intrinsic::Contains { haystack, needle } => {
                collect_expr_reads(haystack, fn_name, out);
                collect_expr_reads(needle, fn_name, out);
            }
            Intrinsic::Print(args) => {
                for a in args {
                    collect_expr_reads(a, fn_name, out);
                }
            }
        },
        _ => {}
    }
}

fn pat_matches(pat: &MatchPat, val: &Value) -> bool {
    match (pat, val) {
        (MatchPat::Wildcard, _) => true,
        (MatchPat::Int(a), Value::Int(b)) => a == b,
        (MatchPat::Str(a), Value::Str(b)) => a == b,
        (
            MatchPat::EnumVariant {
                enum_name: ea,
                variant: va,
            },
            Value::EnumVariant {
                enum_name: eb,
                variant: vb,
            },
        ) => ea == eb && va == vb,
        _ => false,
    }
}

fn combine_assign(cur: Value, op: AssignOp, rhs: Value) -> Result<Value, String> {
    match op {
        AssignOp::Set => Ok(rhs),
        AssignOp::AddAssign => eval_binop(BinOp::Add, cur, rhs),
        AssignOp::SubAssign => eval_binop(BinOp::Sub, cur, rhs),
    }
}

fn eval_binop(op: BinOp, lv: Value, rv: Value) -> Result<Value, String> {
    match (op, lv, rv) {
        (BinOp::Add, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_add(b))),
        (BinOp::Add, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
        (BinOp::Add, Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{}{}", a, b))),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_sub(b))),
        (BinOp::Sub, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_mul(b))),
        (BinOp::Mul, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
        (BinOp::Div | BinOp::IntDiv, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
        (BinOp::Div | BinOp::IntDiv, Value::Int(a), Value::Int(b)) => {
            if b == 0 {
                Err("division by zero".to_string())
            } else {
                Ok(Value::Int(a.wrapping_div(b)))
            }
        }
        (BinOp::Mod, Value::Int(a), Value::Int(b)) => {
            if b == 0 {
                Err("modulo by zero".to_string())
            } else {
                Ok(Value::Int(a.wrapping_rem(b)))
            }
        }
        (BinOp::Eq, a, b) => Ok(Value::Bool(a == b)),
        (BinOp::Ne, a, b) => Ok(Value::Bool(a != b)),
        (BinOp::Lt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
        (BinOp::Lt, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a < b)),
        (BinOp::Lt, Value::Str(a), Value::Str(b)) => Ok(Value::Bool(a < b)),
        (BinOp::Le, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
        (BinOp::Le, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a <= b)),
        (BinOp::Le, Value::Str(a), Value::Str(b)) => Ok(Value::Bool(a <= b)),
        (BinOp::Gt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
        (BinOp::Gt, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a > b)),
        (BinOp::Gt, Value::Str(a), Value::Str(b)) => Ok(Value::Bool(a > b)),
        (BinOp::Ge, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
        (BinOp::Ge, Value::Float(a), Value::Float(b)) => Ok(Value::Bool(a >= b)),
        (BinOp::Ge, Value::Str(a), Value::Str(b)) => Ok(Value::Bool(a >= b)),
        _ => Err("binary operator type mismatch".to_string()),
    }
}

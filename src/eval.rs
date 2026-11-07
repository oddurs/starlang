use std::collections::{BTreeMap, HashMap};

use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, MatchPat, NodeId,
    Stmt, UnaryOp,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    List(Vec<Value>),
    Struct {
        name: String,
        fields: BTreeMap<String, Value>,
    },
    EnumVariant {
        enum_name: String,
        variant: String,
    },
    Void,
}

impl Value {
    pub fn display_str(&self) -> String {
        match self {
            Value::Int(v) => v.to_string(),
            Value::Float(v) => format!("{}", v),
            Value::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Value::Str(s) => s.clone(),
            Value::List(items) => {
                let inner: Vec<String> = items.iter().map(|i| i.display_str()).collect();
                format!("[{}]", inner.join(", "))
            }
            Value::Struct { name, fields } => {
                let inner: Vec<String> = fields
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v.display_str()))
                    .collect();
                format!("{} {{ {} }}", name, inner.join(", "))
            }
            Value::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
            Value::Void => "()".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct EvalResult {
    pub ok: bool,
    pub stdout: String,
    pub steps: usize,
    pub error: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestResult {
    pub name: String,
    pub passed: bool,
    pub steps: usize,
    pub stdout: String,
    pub error: Option<String>,
}

enum Flow {
    Next,
    Break,
    Continue,
    Return(Value),
}

const DEFAULT_MAX_STEPS: usize = 100_000;
const MAX_CALL_DEPTH: usize = 128;

pub trait VmObserver {
    fn on_stmt(&mut self, node_id: NodeId);
    fn on_call_enter(&mut self, depth: usize, name: &str, args: &[Value]) -> Option<usize>;
    fn on_call_exit(&mut self, slot: Option<usize>, name: &str, ret: &Value, steps_delta: usize);
}

pub fn eval_module_default(hub: &HubModule) -> EvalResult {
    eval_module(hub, DEFAULT_MAX_STEPS)
}

pub fn eval_module(hub: &HubModule, max_steps: usize) -> EvalResult {
    if !hub.has_main() {
        return EvalResult {
            ok: true,
            stdout: String::new(),
            steps: 0,
            error: None,
        };
    }

    let mut fns: HashMap<&str, &FnDecl> = HashMap::new();
    for item in &hub.items {
        if let Item::Function(f) = item {
            fns.insert(f.name.as_str(), f);
        }
    }

    let mut vm = HubVm {
        fns,
        stdout: String::new(),
        steps: 0,
        max_steps,
        depth: 0,
        observer: None,
    };

    match vm.call_fn("main", Vec::new()) {
        Ok(_) => EvalResult {
            ok: true,
            stdout: vm.stdout,
            steps: vm.steps,
            error: None,
        },
        Err(err) => EvalResult {
            ok: false,
            stdout: vm.stdout,
            steps: vm.steps,
            error: Some(err),
        },
    }
}

pub fn eval_tests_default(hub: &HubModule) -> Vec<TestResult> {
    eval_tests(hub, DEFAULT_MAX_STEPS)
}

pub fn eval_tests(hub: &HubModule, max_steps_per_test: usize) -> Vec<TestResult> {
    let mut fns: HashMap<&str, &FnDecl> = HashMap::new();
    for item in &hub.items {
        if let Item::Function(f) = item {
            fns.insert(f.name.as_str(), f);
        }
    }

    let mut out = Vec::new();
    for item in &hub.items {
        if let Item::Test(t) = item {
            let mut vm = HubVm {
                fns: fns.clone(),
                stdout: String::new(),
                steps: 0,
                max_steps: max_steps_per_test,
                depth: 0,
                observer: None,
            };
            let mut scopes = Scopes::new();
            match vm.exec_block(&t.body, &mut scopes) {
                Ok(Flow::Next | Flow::Return(_)) => out.push(TestResult {
                    name: t.name.clone(),
                    passed: true,
                    steps: vm.steps,
                    stdout: vm.stdout,
                    error: None,
                }),
                Ok(Flow::Break) => out.push(TestResult {
                    name: t.name.clone(),
                    passed: false,
                    steps: vm.steps,
                    stdout: vm.stdout,
                    error: Some("'break' escaped test body".to_string()),
                }),
                Ok(Flow::Continue) => out.push(TestResult {
                    name: t.name.clone(),
                    passed: false,
                    steps: vm.steps,
                    stdout: vm.stdout,
                    error: Some("'continue' escaped test body".to_string()),
                }),
                Err(err) => out.push(TestResult {
                    name: t.name.clone(),
                    passed: false,
                    steps: vm.steps,
                    stdout: vm.stdout,
                    error: Some(err),
                }),
            }
        }
    }
    out
}

pub fn eval_with_observer(
    hub: &HubModule,
    max_steps: usize,
    observer: &mut dyn VmObserver,
) -> Result<(), String> {
    let mut fns: HashMap<&str, &FnDecl> = HashMap::new();
    for item in &hub.items {
        if let Item::Function(f) = item {
            fns.insert(f.name.as_str(), f);
        }
    }

    if hub.has_main() {
        let mut vm = HubVm {
            fns: fns.clone(),
            stdout: String::new(),
            steps: 0,
            max_steps,
            depth: 0,
            observer: Some(observer),
        };
        let _ = vm.call_fn("main", Vec::new())?;
    }

    for item in &hub.items {
        if let Item::Test(t) = item {
            let mut vm = HubVm {
                fns: fns.clone(),
                stdout: String::new(),
                steps: 0,
                max_steps,
                depth: 0,
                observer: Some(observer),
            };
            let mut scopes = Scopes::new();
            let _ = vm.exec_block(&t.body, &mut scopes)?;
        }
    }

    Ok(())
}

struct HubVm<'a, 'b> {
    fns: HashMap<&'a str, &'a FnDecl>,
    stdout: String,
    steps: usize,
    max_steps: usize,
    depth: usize,
    observer: Option<&'b mut dyn VmObserver>,
}

struct Scopes {
    frames: Vec<HashMap<String, Value>>,
}

impl Scopes {
    fn new() -> Self {
        Self {
            frames: vec![HashMap::new()],
        }
    }

    fn push(&mut self) {
        self.frames.push(HashMap::new());
    }

    fn pop(&mut self) {
        self.frames.pop();
    }

    fn define(&mut self, name: String, val: Value) {
        if let Some(top) = self.frames.last_mut() {
            top.insert(name, val);
        }
    }

    fn get(&self, name: &str) -> Option<&Value> {
        for frame in self.frames.iter().rev() {
            if let Some(v) = frame.get(name) {
                return Some(v);
            }
        }
        None
    }

    fn get_mut(&mut self, name: &str) -> Option<&mut Value> {
        for frame in self.frames.iter_mut().rev() {
            if let Some(v) = frame.get_mut(name) {
                return Some(v);
            }
        }
        None
    }
}

impl<'a, 'b> HubVm<'a, 'b> {
    fn tick(&mut self) -> Result<(), String> {
        self.steps += 1;
        if self.steps > self.max_steps {
            Err(format!(
                "step budget ({}) exceeded — possible infinite loop",
                self.max_steps
            ))
        } else {
            Ok(())
        }
    }

    fn call_fn(&mut self, name: &str, args: Vec<Value>) -> Result<Value, String> {
        self.tick()?;
        let Some(decl) = self.fns.get(name).copied() else {
            return Err(format!("undefined function '{}'", name));
        };
        if args.len() != decl.params.len() {
            return Err(format!(
                "function '{}' expected {} arg(s), got {}",
                name,
                decl.params.len(),
                args.len()
            ));
        }
        if self.depth >= MAX_CALL_DEPTH {
            return Err(format!(
                "call stack depth ({}) exceeded in '{}'",
                MAX_CALL_DEPTH, name
            ));
        }

        let start_steps = self.steps;
        let trace_slot = self
            .observer
            .as_deref_mut()
            .and_then(|obs| obs.on_call_enter(self.depth, name, &args));

        self.depth += 1;
        let mut scopes = Scopes::new();
        for (param, val) in decl.params.iter().zip(args) {
            scopes.define(param.name.clone(), val);
        }
        let res = self.exec_block(&decl.body, &mut scopes);
        self.depth -= 1;

        let ret_val = match res? {
            Flow::Return(v) => v,
            Flow::Next => Value::Void,
            Flow::Break => return Err("'break' escaped function body".to_string()),
            Flow::Continue => return Err("'continue' escaped function body".to_string()),
        };

        let steps_delta = self.steps.saturating_sub(start_steps);
        if let Some(obs) = self.observer.as_deref_mut() {
            obs.on_call_exit(trace_slot, name, &ret_val, steps_delta);
        }

        Ok(ret_val)
    }

    fn exec_block(&mut self, stmts: &[Stmt], scopes: &mut Scopes) -> Result<Flow, String> {
        scopes.push();
        let mut flow = Flow::Next;
        for stmt in stmts {
            flow = self.exec_stmt(stmt, scopes)?;
            if !matches!(flow, Flow::Next) {
                break;
            }
        }
        scopes.pop();
        Ok(flow)
    }

    fn exec_stmt(&mut self, stmt: &Stmt, scopes: &mut Scopes) -> Result<Flow, String> {
        self.tick()?;
        if let Some(id) = exec_stmt_id(stmt) {
            if let Some(obs) = self.observer.as_deref_mut() {
                obs.on_stmt(id);
            }
        }
        match stmt {
            Stmt::Comment { .. } => Ok(Flow::Next),
            Stmt::Let { name, value, .. } => {
                let val = self.eval_expr(value, scopes)?;
                scopes.define(name.clone(), val);
                Ok(Flow::Next)
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let rhs = self.eval_expr(value, scopes)?;
                match target {
                    AssignTarget::Var(var) => {
                        let Some(slot) = scopes.get_mut(var) else {
                            return Err(format!("assignment to undeclared variable '{}'", var));
                        };
                        *slot = apply_assign_op(*op, slot.clone(), rhs)?;
                    }
                    AssignTarget::Field { base, field } => {
                        let Some(slot) = scopes.get_mut(base) else {
                            return Err(format!("assignment to undeclared struct '{}'", base));
                        };
                        if let Value::Struct { fields, .. } = slot {
                            let prev = fields
                                .get(field)
                                .cloned()
                                .ok_or_else(|| format!("unknown field '{}'", field))?;
                            let updated = apply_assign_op(*op, prev, rhs)?;
                            fields.insert(field.clone(), updated);
                        } else {
                            return Err(format!("'{}' is not a struct", base));
                        }
                    }
                    AssignTarget::Index { base, index } => {
                        let idx_val = self.eval_expr(index, scopes)?;
                        let Value::Int(idx) = idx_val else {
                            return Err("list index must be Int".to_string());
                        };
                        let Some(slot) = scopes.get_mut(base) else {
                            return Err(format!("assignment to undeclared list '{}'", base));
                        };
                        if let Value::List(items) = slot {
                            if idx < 0 || (idx as usize) >= items.len() {
                                return Err(format!(
                                    "index {} out of bounds (len {})",
                                    idx,
                                    items.len()
                                ));
                            }
                            let prev = items[idx as usize].clone();
                            items[idx as usize] = apply_assign_op(*op, prev, rhs)?;
                        } else {
                            return Err(format!("'{}' is not a list", base));
                        }
                    }
                }
                Ok(Flow::Next)
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let c = self.eval_expr(cond, scopes)?;
                let Value::Bool(b) = c else {
                    return Err("if condition must evaluate to Bool".to_string());
                };
                if b {
                    self.exec_block(then_body, scopes)
                } else {
                    self.exec_block(else_body, scopes)
                }
            }
            Stmt::Match { expr, arms, .. } => {
                let scrutinee = self.eval_expr(expr, scopes)?;
                for arm in arms {
                    if pat_matches(&arm.pat, &scrutinee) {
                        return self.exec_block(&arm.body, scopes);
                    }
                }
                Ok(Flow::Next)
            }
            Stmt::While { cond, body, .. } => {
                loop {
                    let c = self.eval_expr(cond, scopes)?;
                    let Value::Bool(b) = c else {
                        return Err("while condition must evaluate to Bool".to_string());
                    };
                    if !b {
                        break;
                    }
                    match self.exec_block(body, scopes)? {
                        Flow::Next | Flow::Continue => {}
                        Flow::Break => break,
                        Flow::Return(v) => return Ok(Flow::Return(v)),
                    }
                }
                Ok(Flow::Next)
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let iter_val = self.eval_expr(iter, scopes)?;
                let Value::List(items) = iter_val else {
                    return Err("for-each target must evaluate to List".to_string());
                };
                for elem in items {
                    scopes.push();
                    scopes.define(var.clone(), elem);
                    let flow = self.exec_block(body, scopes)?;
                    scopes.pop();
                    match flow {
                        Flow::Next | Flow::Continue => {}
                        Flow::Break => break,
                        Flow::Return(v) => return Ok(Flow::Return(v)),
                    }
                }
                Ok(Flow::Next)
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                let s_val = self.eval_expr(start, scopes)?;
                let e_val = self.eval_expr(end, scopes)?;
                let (Value::Int(s), Value::Int(e)) = (s_val, e_val) else {
                    return Err("for-range bounds must evaluate to Int".to_string());
                };
                let mut cur = s;
                while cur < e {
                    scopes.push();
                    scopes.define(var.clone(), Value::Int(cur));
                    let flow = self.exec_block(body, scopes)?;
                    scopes.pop();
                    match flow {
                        Flow::Next | Flow::Continue => {}
                        Flow::Break => break,
                        Flow::Return(v) => return Ok(Flow::Return(v)),
                    }
                    cur += 1;
                }
                Ok(Flow::Next)
            }
            Stmt::Break { .. } => Ok(Flow::Break),
            Stmt::Continue { .. } => Ok(Flow::Continue),
            Stmt::Return { value, .. } => {
                let val = match value {
                    Some(e) => self.eval_expr(e, scopes)?,
                    None => Value::Void,
                };
                Ok(Flow::Return(val))
            }
            Stmt::Assert { cond, .. } => {
                let val = self.eval_expr(cond, scopes)?;
                match val {
                    Value::Bool(true) => Ok(Flow::Next),
                    Value::Bool(false) => Err("assertion failed".to_string()),
                    _ => Err("assert condition must evaluate to Bool".to_string()),
                }
            }
            Stmt::AssertEq { left, right, .. } => {
                let lv = self.eval_expr(left, scopes)?;
                let rv = self.eval_expr(right, scopes)?;
                if lv == rv {
                    Ok(Flow::Next)
                } else {
                    Err(format!(
                        "assert_eq failed: left = {}, right = {}",
                        lv.display_str(),
                        rv.display_str()
                    ))
                }
            }
            Stmt::Expr { expr, .. } => {
                let _ = self.eval_expr(expr, scopes)?;
                Ok(Flow::Next)
            }
        }
    }

    fn eval_expr(&mut self, expr: &Expr, scopes: &mut Scopes) -> Result<Value, String> {
        self.tick()?;
        match expr {
            Expr::Int(v) => Ok(Value::Int(*v)),
            Expr::Float(v) => Ok(Value::Float(*v)),
            Expr::Bool(b) => Ok(Value::Bool(*b)),
            Expr::Str(s) => Ok(Value::Str(s.clone())),
            Expr::Var(name) => scopes
                .get(name)
                .cloned()
                .ok_or_else(|| format!("undeclared variable '{}'", name)),
            Expr::EnumVariant { enum_name, variant } => Ok(Value::EnumVariant {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
            }),
            Expr::List(items) => {
                let mut vals = Vec::with_capacity(items.len());
                for it in items {
                    vals.push(self.eval_expr(it, scopes)?);
                }
                Ok(Value::List(vals))
            }
            Expr::StructInit { name, fields } => {
                let mut map = BTreeMap::new();
                for (fname, fexpr) in fields {
                    map.insert(fname.clone(), self.eval_expr(fexpr, scopes)?);
                }
                Ok(Value::Struct {
                    name: name.clone(),
                    fields: map,
                })
            }
            Expr::FieldAccess { base, field } => {
                let b = self.eval_expr(base, scopes)?;
                if let Value::Struct { fields, .. } = b {
                    fields
                        .get(field)
                        .cloned()
                        .ok_or_else(|| format!("missing struct field '{}'", field))
                } else {
                    Err(format!("field access '.{}' on non-struct", field))
                }
            }
            Expr::Index { base, index } => {
                let b = self.eval_expr(base, scopes)?;
                let idx = self.eval_expr(index, scopes)?;
                let Value::Int(i) = idx else {
                    return Err("index must be Int".to_string());
                };
                match b {
                    Value::List(items) => {
                        if i < 0 || (i as usize) >= items.len() {
                            Err(format!("index {} out of bounds (len {})", i, items.len()))
                        } else {
                            Ok(items[i as usize].clone())
                        }
                    }
                    _ => Err("indexing non-list value".to_string()),
                }
            }
            Expr::Unary { op, expr: inner } => {
                let v = self.eval_expr(inner, scopes)?;
                match (op, v) {
                    (UnaryOp::Neg, Value::Int(n)) => Ok(Value::Int(-n)),
                    (UnaryOp::Neg, Value::Float(n)) => Ok(Value::Float(-n)),
                    (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
                    _ => Err("invalid operand for unary operator".to_string()),
                }
            }
            Expr::Binary { op, left, right } => {
                if *op == BinOp::And {
                    let Value::Bool(l) = self.eval_expr(left, scopes)? else {
                        return Err("&& expects Bool".to_string());
                    };
                    if !l {
                        return Ok(Value::Bool(false));
                    }
                    let Value::Bool(r) = self.eval_expr(right, scopes)? else {
                        return Err("&& expects Bool".to_string());
                    };
                    return Ok(Value::Bool(r));
                }
                if *op == BinOp::Or {
                    let Value::Bool(l) = self.eval_expr(left, scopes)? else {
                        return Err("|| expects Bool".to_string());
                    };
                    if l {
                        return Ok(Value::Bool(true));
                    }
                    let Value::Bool(r) = self.eval_expr(right, scopes)? else {
                        return Err("|| expects Bool".to_string());
                    };
                    return Ok(Value::Bool(r));
                }
                let l = self.eval_expr(left, scopes)?;
                let r = self.eval_expr(right, scopes)?;
                eval_binop(*op, l, r)
            }
            Expr::Call { func, args } => {
                let mut arg_vals = Vec::with_capacity(args.len());
                for a in args {
                    arg_vals.push(self.eval_expr(a, scopes)?);
                }
                self.call_fn(func, arg_vals)
            }
            Expr::Intrinsic(intr) => self.eval_intrinsic(intr, scopes),
        }
    }

    fn eval_intrinsic(&mut self, intr: &Intrinsic, scopes: &mut Scopes) -> Result<Value, String> {
        match intr {
            Intrinsic::Len(e) => match self.eval_expr(e, scopes)? {
                Value::List(items) => Ok(Value::Int(items.len() as i64)),
                Value::Str(s) => Ok(Value::Int(s.len() as i64)),
                _ => Err("len() expects List or Str".to_string()),
            },
            Intrinsic::Min(a, b) => {
                let va = self.eval_expr(a, scopes)?;
                let vb = self.eval_expr(b, scopes)?;
                match (va, vb) {
                    (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x.min(y))),
                    (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x.min(y))),
                    _ => Err("min() expects matching numeric types".to_string()),
                }
            }
            Intrinsic::Max(a, b) => {
                let va = self.eval_expr(a, scopes)?;
                let vb = self.eval_expr(b, scopes)?;
                match (va, vb) {
                    (Value::Int(x), Value::Int(y)) => Ok(Value::Int(x.max(y))),
                    (Value::Float(x), Value::Float(y)) => Ok(Value::Float(x.max(y))),
                    _ => Err("max() expects matching numeric types".to_string()),
                }
            }
            Intrinsic::Abs(a) => match self.eval_expr(a, scopes)? {
                Value::Int(x) => Ok(Value::Int(x.abs())),
                Value::Float(x) => Ok(Value::Float(x.abs())),
                _ => Err("abs() expects Int or Float".to_string()),
            },
            Intrinsic::Push { list, value } => {
                let Expr::Var(var_name) = list else {
                    return Err("push target must be a list variable".to_string());
                };
                let pushed = self.eval_expr(value, scopes)?;
                let Some(slot) = scopes.get_mut(var_name) else {
                    return Err(format!("push to undeclared variable '{}'", var_name));
                };
                if let Value::List(items) = slot {
                    items.push(pushed);
                    Ok(Value::Void)
                } else {
                    Err(format!("'{}' is not a list", var_name))
                }
            }
            Intrinsic::Print(args) => {
                let mut parts = Vec::with_capacity(args.len());
                for a in args {
                    parts.push(self.eval_expr(a, scopes)?.display_str());
                }
                self.stdout.push_str(&parts.join(" "));
                self.stdout.push('\n');
                Ok(Value::Void)
            }
            Intrinsic::Contains { haystack, needle } => {
                let h = self.eval_expr(haystack, scopes)?;
                let n = self.eval_expr(needle, scopes)?;
                match (h, n) {
                    (Value::Str(hs), Value::Str(ns)) => Ok(Value::Bool(hs.contains(&ns))),
                    (Value::List(items), target) => {
                        Ok(Value::Bool(items.iter().any(|x| *x == target)))
                    }
                    _ => Err("contains() expects (Str, Str) or (List<T>, T)".to_string()),
                }
            }
            Intrinsic::Upper(e) => match self.eval_expr(e, scopes)? {
                Value::Str(s) => Ok(Value::Str(s.to_uppercase())),
                _ => Err("upper() expects Str".to_string()),
            },
            Intrinsic::Lower(e) => match self.eval_expr(e, scopes)? {
                Value::Str(s) => Ok(Value::Str(s.to_lowercase())),
                _ => Err("lower() expects Str".to_string()),
            },
            Intrinsic::ToStr(e) => {
                let v = self.eval_expr(e, scopes)?;
                Ok(Value::Str(v.display_str()))
            }
        }
    }
}

pub fn exec_stmt_id(stmt: &Stmt) -> Option<NodeId> {
    match stmt {
        Stmt::Comment { .. } => None,
        Stmt::Let { id, .. }
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
        | Stmt::Expr { id, .. } => Some(*id),
    }
}

fn pat_matches(pat: &MatchPat, val: &Value) -> bool {
    match (pat, val) {
        (MatchPat::Wildcard, _) => true,
        (
            MatchPat::EnumVariant {
                enum_name: pe,
                variant: pv,
            },
            Value::EnumVariant {
                enum_name: ve,
                variant: vv,
            },
        ) => pe == ve && pv == vv,
        (MatchPat::Int(p), Value::Int(v)) => p == v,
        (MatchPat::Str(p), Value::Str(v)) => p == v,
        _ => false,
    }
}

fn apply_assign_op(op: AssignOp, lhs: Value, rhs: Value) -> Result<Value, String> {
    match op {
        AssignOp::Set => Ok(rhs),
        AssignOp::AddAssign => eval_binop(BinOp::Add, lhs, rhs),
        AssignOp::SubAssign => eval_binop(BinOp::Sub, lhs, rhs),
    }
}

fn eval_binop(op: BinOp, l: Value, r: Value) -> Result<Value, String> {
    match (op, l, r) {
        (BinOp::Add, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_add(b))),
        (BinOp::Add, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
        (BinOp::Add, Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{}{}", a, b))),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_sub(b))),
        (BinOp::Sub, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_mul(b))),
        (BinOp::Mul, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
        (BinOp::Div | BinOp::IntDiv, Value::Int(a), Value::Int(b)) => {
            if b == 0 {
                Err("integer division by zero".to_string())
            } else {
                Ok(Value::Int(a / b))
            }
        }
        (BinOp::Div | BinOp::IntDiv, Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
        (BinOp::Mod, Value::Int(a), Value::Int(b)) => {
            if b == 0 {
                Err("modulo by zero".to_string())
            } else {
                Ok(Value::Int(a % b))
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
        _ => Err(format!("type mismatch for binary operator {:?}", op)),
    }
}

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use crate::eval::eval_fn_call;
use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, MatchPat, NodeId,
    Stmt, Type, UnaryOp,
};

const INF: i64 = 1_000_000_000_000;
const WITNESS_STEP_BUDGET: usize = 5_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObligationKind {
    DivByZero,
    IndexBounds,
    Assertion,
}

impl ObligationKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            ObligationKind::DivByZero => "div_by_zero",
            ObligationKind::IndexBounds => "index_bounds",
            ObligationKind::Assertion => "assertion",
        }
    }

    pub fn label(&self) -> &'static str {
        match self {
            ObligationKind::DivByZero => "Division / Modulo Non-Zero",
            ObligationKind::IndexBounds => "List Index In-Bounds",
            ObligationKind::Assertion => "Inline Contract Assertion",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyStatus {
    ProvenSafe,
    Refuted { witness_call: String, runtime_error: String },
    UnprovenWarning,
}

impl VerifyStatus {
    pub fn as_str(&self) -> &'static str {
        match self {
            VerifyStatus::ProvenSafe => "safe",
            VerifyStatus::Refuted { .. } => "refuted",
            VerifyStatus::UnprovenWarning => "warning",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafetyObligation {
    pub id: usize,
    pub func: String,
    pub kind: ObligationKind,
    pub expr_summary: String,
    pub status: VerifyStatus,
    pub proof_note: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnreachableBranch {
    pub func: String,
    pub stmt_id: NodeId,
    pub branch: &'static str,
    pub cond_summary: String,
    pub reason: String,
}

#[derive(Debug, Clone)]
pub struct VerifyReport {
    pub total_obligations: usize,
    pub proven_safe: usize,
    pub refuted: usize,
    pub warnings: usize,
    pub obligations: Vec<SafetyObligation>,
    pub unreachable_branches: Vec<UnreachableBranch>,
    pub elapsed_ms: u128,
}

impl VerifyReport {
    pub fn all_safe(&self) -> bool {
        self.refuted == 0 && self.warnings == 0 && self.unreachable_branches.is_empty()
    }
}

/// Abstract integer interval `[lo, hi]` with finite disequality exclusions (`not_eq`).
#[derive(Debug, Clone, PartialEq, Eq)]
struct IntDomain {
    lo: i64,
    hi: i64,
    not_eq: BTreeSet<i64>,
}

impl IntDomain {
    fn top() -> Self {
        Self {
            lo: -INF,
            hi: INF,
            not_eq: BTreeSet::new(),
        }
    }

    fn non_negative() -> Self {
        Self {
            lo: 0,
            hi: INF,
            not_eq: BTreeSet::new(),
        }
    }

    fn constant(v: i64) -> Self {
        let c = v.clamp(-INF, INF);
        Self {
            lo: c,
            hi: c,
            not_eq: BTreeSet::new(),
        }
    }

    fn range(lo: i64, hi: i64) -> Self {
        let mut d = Self {
            lo: lo.clamp(-INF, INF),
            hi: hi.clamp(-INF, INF),
            not_eq: BTreeSet::new(),
        };
        d.normalize();
        d
    }

    fn normalize(&mut self) {
        self.lo = self.lo.clamp(-INF, INF);
        self.hi = self.hi.clamp(-INF, INF);
        while self.lo <= self.hi && self.not_eq.contains(&self.lo) {
            self.lo += 1;
        }
        while self.lo <= self.hi && self.not_eq.contains(&self.hi) {
            self.hi -= 1;
        }
        self.not_eq.retain(|&x| x > self.lo && x < self.hi);
    }

    fn is_empty(&self) -> bool {
        self.lo > self.hi
    }

    fn contains(&self, v: i64) -> bool {
        v >= self.lo && v <= self.hi && !self.not_eq.contains(&v)
    }

    fn intersect(&self, other: &Self) -> Self {
        let mut not_eq: BTreeSet<i64> = self.not_eq.union(&other.not_eq).copied().collect();
        if not_eq.len() > 16 {
            not_eq.clear();
        }
        let mut out = Self {
            lo: self.lo.max(other.lo),
            hi: self.hi.min(other.hi),
            not_eq,
        };
        out.normalize();
        out
    }

    fn join(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }
        let lo = self.lo.min(other.lo);
        let hi = self.hi.max(other.hi);
        let mut not_eq = BTreeSet::new();
        for &x in &self.not_eq {
            if !other.contains(x) {
                not_eq.insert(x);
            }
        }
        for &x in &other.not_eq {
            if !self.contains(x) {
                not_eq.insert(x);
            }
        }
        let mut out = Self { lo, hi, not_eq };
        out.normalize();
        out
    }

    /// Cousot & Cousot interval widening `self ∇ next`.
    fn widen(&self, next: &Self) -> Self {
        if self.is_empty() {
            return next.clone();
        }
        if next.is_empty() {
            return self.clone();
        }
        let lo = if next.lo < self.lo { -INF } else { self.lo };
        let hi = if next.hi > self.hi { INF } else { self.hi };
        let not_eq: BTreeSet<i64> = self
            .not_eq
            .intersection(&next.not_eq)
            .copied()
            .filter(|&x| x > lo && x < hi)
            .collect();
        let mut out = Self { lo, hi, not_eq };
        out.normalize();
        out
    }

    fn exclude(&mut self, val: i64) {
        if val >= self.lo && val <= self.hi {
            self.not_eq.insert(val);
            self.normalize();
        }
    }

    fn display(&self) -> String {
        let fmt_b = |v: i64| -> String {
            if v <= -INF + 1000 {
                "-∞".to_string()
            } else if v >= INF - 1000 {
                "+∞".to_string()
            } else {
                v.to_string()
            }
        };
        if self.lo == self.hi {
            format!("[{}]", fmt_b(self.lo))
        } else if self.not_eq.contains(&0) {
            format!("[{}, {}] \\ {{0}}", fmt_b(self.lo), fmt_b(self.hi))
        } else {
            format!("[{}, {}]", fmt_b(self.lo), fmt_b(self.hi))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BoolDomain {
    can_false: bool,
    can_true: bool,
}

impl BoolDomain {
    fn top() -> Self {
        Self {
            can_false: true,
            can_true: true,
        }
    }

    fn constant(b: bool) -> Self {
        Self {
            can_false: !b,
            can_true: b,
        }
    }

    fn is_empty(&self) -> bool {
        !self.can_false && !self.can_true
    }

    fn join(&self, other: &Self) -> Self {
        Self {
            can_false: self.can_false || other.can_false,
            can_true: self.can_true || other.can_true,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SymState {
    ints: BTreeMap<String, IntDomain>,
    lens: BTreeMap<String, IntDomain>,
    bools: BTreeMap<String, BoolDomain>,
    /// Variables initialized as `let n = xs.len()`: narrowing `n` also narrows `lens[xs]`.
    len_aliases: BTreeMap<String, String>,
    /// Relational facts `(idx_var, list_var)` representing `idx_var < len(list_var)`.
    strict_lt_len: BTreeSet<(String, String)>,
}

impl SymState {
    fn from_fn(f: &FnDecl) -> Self {
        let mut ints = BTreeMap::new();
        let mut lens = BTreeMap::new();
        let mut bools = BTreeMap::new();
        for p in &f.params {
            match &p.ty {
                Type::Int => {
                    ints.insert(p.name.clone(), IntDomain::top());
                }
                Type::Bool => {
                    bools.insert(p.name.clone(), BoolDomain::top());
                }
                Type::List(_) | Type::Str => {
                    lens.insert(p.name.clone(), IntDomain::non_negative());
                }
                _ => {}
            }
        }
        Self {
            ints,
            lens,
            bools,
            len_aliases: BTreeMap::new(),
            strict_lt_len: BTreeSet::new(),
        }
    }

    fn int_dom(&self, name: &str) -> IntDomain {
        self.ints.get(name).cloned().unwrap_or_else(IntDomain::top)
    }

    fn len_dom(&self, name: &str) -> IntDomain {
        self.lens
            .get(name)
            .cloned()
            .unwrap_or_else(IntDomain::non_negative)
    }

    fn bool_dom(&self, name: &str) -> BoolDomain {
        self.bools
            .get(name)
            .copied()
            .unwrap_or_else(BoolDomain::top)
    }

    fn set_int(&mut self, name: &str, dom: IntDomain) {
        self.ints.insert(name.to_string(), dom);
        self.len_aliases.remove(name);
        self.strict_lt_len.retain(|(iv, _)| iv != name);
    }

    fn narrow_int(&mut self, name: &str, narrowed: IntDomain) -> bool {
        if narrowed.is_empty() {
            return false;
        }
        self.ints.insert(name.to_string(), narrowed.clone());
        if let Some(list_var) = self.len_aliases.get(name).cloned() {
            let merged_len = self.len_dom(&list_var).intersect(&narrowed);
            if merged_len.is_empty() {
                return false;
            }
            self.lens.insert(list_var, merged_len);
        }
        true
    }

    fn narrow_len(&mut self, list_var: &str, narrowed: IntDomain) -> bool {
        let merged = self
            .len_dom(list_var)
            .intersect(&narrowed)
            .intersect(&IntDomain::non_negative());
        if merged.is_empty() {
            return false;
        }
        self.lens.insert(list_var.to_string(), merged.clone());
        let aliases: Vec<String> = self
            .len_aliases
            .iter()
            .filter_map(|(k, v)| if v == list_var { Some(k.clone()) } else { None })
            .collect();
        for a in aliases {
            let cur = self.int_dom(&a).intersect(&merged);
            if cur.is_empty() {
                return false;
            }
            self.ints.insert(a, cur);
        }
        true
    }

    fn join(&self, other: &Self) -> Self {
        let mut ints = BTreeMap::new();
        let all_int_keys: BTreeSet<&String> = self.ints.keys().chain(other.ints.keys()).collect();
        for k in all_int_keys {
            ints.insert(k.clone(), self.int_dom(k).join(&other.int_dom(k)));
        }

        let mut lens = BTreeMap::new();
        let all_len_keys: BTreeSet<&String> = self.lens.keys().chain(other.lens.keys()).collect();
        for k in all_len_keys {
            lens.insert(k.clone(), self.len_dom(k).join(&other.len_dom(k)));
        }

        let mut bools = BTreeMap::new();
        let all_bool_keys: BTreeSet<&String> =
            self.bools.keys().chain(other.bools.keys()).collect();
        for k in all_bool_keys {
            bools.insert(k.clone(), self.bool_dom(k).join(&other.bool_dom(k)));
        }

        let mut len_aliases = BTreeMap::new();
        for (k, v) in &self.len_aliases {
            if other.len_aliases.get(k) == Some(v) {
                len_aliases.insert(k.clone(), v.clone());
            }
        }

        let strict_lt_len: BTreeSet<(String, String)> = self
            .strict_lt_len
            .intersection(&other.strict_lt_len)
            .cloned()
            .collect();

        Self {
            ints,
            lens,
            bools,
            len_aliases,
            strict_lt_len,
        }
    }

    fn widen(&self, next: &Self) -> Self {
        let mut ints = BTreeMap::new();
        let all_int_keys: BTreeSet<&String> = self.ints.keys().chain(next.ints.keys()).collect();
        for k in all_int_keys {
            ints.insert(k.clone(), self.int_dom(k).widen(&next.int_dom(k)));
        }

        let mut lens = BTreeMap::new();
        let all_len_keys: BTreeSet<&String> = self.lens.keys().chain(next.lens.keys()).collect();
        for k in all_len_keys {
            lens.insert(
                k.clone(),
                self.len_dom(k)
                    .widen(&next.len_dom(k))
                    .intersect(&IntDomain::non_negative()),
            );
        }

        let mut bools = BTreeMap::new();
        let all_bool_keys: BTreeSet<&String> = self.bools.keys().chain(next.bools.keys()).collect();
        for k in all_bool_keys {
            bools.insert(k.clone(), self.bool_dom(k).join(&next.bool_dom(k)));
        }

        let mut len_aliases = BTreeMap::new();
        for (k, v) in &self.len_aliases {
            if next.len_aliases.get(k) == Some(v) {
                len_aliases.insert(k.clone(), v.clone());
            }
        }

        let strict_lt_len: BTreeSet<(String, String)> = self
            .strict_lt_len
            .intersection(&next.strict_lt_len)
            .cloned()
            .collect();

        Self {
            ints,
            lens,
            bools,
            len_aliases,
            strict_lt_len,
        }
    }
}

/// Run Hub-level symbolic interval & relational path verification across all non-`main`
/// functions in `hub`, validating any candidate safety violations via concolic Hub VM probing.
pub fn verify_module(hub: &HubModule) -> VerifyReport {
    let start = Instant::now();
    let mut verifier = ModuleVerifier {
        hub,
        next_obligation_id: 1,
        obligations: Vec::new(),
        unreachable_branches: Vec::new(),
        boundary_ints: collect_boundary_ints(hub),
    };

    for item in &hub.items {
        if let Item::Function(f) = item {
            let init = SymState::from_fn(f);
            let _ = verifier.analyze_block(&f.name, f, &f.body, init, true);
        }
    }

    let total_obligations = verifier.obligations.len();
    let mut proven_safe = 0usize;
    let mut refuted = 0usize;
    let mut warnings = 0usize;
    for ob in &verifier.obligations {
        match ob.status {
            VerifyStatus::ProvenSafe => proven_safe += 1,
            VerifyStatus::Refuted { .. } => refuted += 1,
            VerifyStatus::UnprovenWarning => warnings += 1,
        }
    }

    VerifyReport {
        total_obligations,
        proven_safe,
        refuted,
        warnings,
        obligations: verifier.obligations,
        unreachable_branches: verifier.unreachable_branches,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

struct ModuleVerifier<'a> {
    hub: &'a HubModule,
    next_obligation_id: usize,
    obligations: Vec<SafetyObligation>,
    unreachable_branches: Vec<UnreachableBranch>,
    boundary_ints: Vec<i64>,
}

impl<'a> ModuleVerifier<'a> {
    /// Analyze `stmts` starting from `state`, returning `None` if all paths exit (`return`/`break`/`continue`)
    /// or become unreachable. When `emit_checks` is false, performs a pure abstract transfer pass for loop widening.
    fn analyze_block(
        &mut self,
        fn_name: &str,
        fn_decl: &FnDecl,
        stmts: &[Stmt],
        mut state: SymState,
        emit_checks: bool,
    ) -> Option<SymState> {
        for stmt in stmts {
            state = self.analyze_stmt(fn_name, fn_decl, stmt, state, emit_checks)?;
        }
        Some(state)
    }

    fn analyze_stmt(
        &mut self,
        fn_name: &str,
        fn_decl: &FnDecl,
        stmt: &Stmt,
        mut state: SymState,
        emit_checks: bool,
    ) -> Option<SymState> {
        match stmt {
            Stmt::Comment { .. } => Some(state),
            Stmt::Let { name, value, .. } => {
                if emit_checks {
                    self.check_expr_obligations(fn_name, fn_decl, value, &state);
                }
                if let Expr::Intrinsic(intr) = value {
                    if let Intrinsic::Len(Expr::Var(list_var)) = intr.as_ref() {
                        let ldom = state.len_dom(list_var);
                        state.ints.insert(name.clone(), ldom);
                        state.len_aliases.insert(name.clone(), list_var.clone());
                        state.strict_lt_len.retain(|(iv, _)| iv != name);
                        return Some(state);
                    }
                }
                if let Expr::List(items) = value {
                    state
                        .lens
                        .insert(name.clone(), IntDomain::constant(items.len() as i64));
                    state.strict_lt_len.retain(|(_, lv)| lv != name);
                    return Some(state);
                }
                if let Expr::Str(s) = value {
                    state
                        .lens
                        .insert(name.clone(), IntDomain::constant(s.len() as i64));
                    return Some(state);
                }
                if let Some(bdom) = eval_bool_domain(value, &state) {
                    state.bools.insert(name.clone(), bdom);
                    return Some(state);
                }
                let idom = eval_int_domain(value, &state);
                state.set_int(name, idom);
                Some(state)
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                if emit_checks {
                    if let AssignTarget::Index { base, index } = target {
                        self.check_expr_obligations(fn_name, fn_decl, index, &state);
                        self.check_index_access(
                            fn_name,
                            fn_decl,
                            &Expr::Var(base.clone()),
                            index,
                            &state,
                        );
                    }
                    self.check_expr_obligations(fn_name, fn_decl, value, &state);
                }
                match target {
                    AssignTarget::Var(v) => {
                        let rhs_dom = eval_int_domain(value, &state);
                        let new_dom = match op {
                            AssignOp::Set => {
                                if let Some(bdom) = eval_bool_domain(value, &state) {
                                    state.bools.insert(v.clone(), bdom);
                                }
                                rhs_dom
                            }
                            AssignOp::AddAssign => add_domains(&state.int_dom(v), &rhs_dom),
                            AssignOp::SubAssign => sub_domains(&state.int_dom(v), &rhs_dom),
                        };
                        state.set_int(v, new_dom);
                    }
                    AssignTarget::Field { .. } | AssignTarget::Index { .. } => {}
                }
                Some(state)
            }
            Stmt::If {
                id,
                cond,
                then_body,
                else_body,
                ..
            } => {
                if emit_checks {
                    self.check_expr_obligations(fn_name, fn_decl, cond, &state);
                }
                let then_in = refine_cond(cond, true, &state);
                let else_in = refine_cond(cond, false, &state);

                if emit_checks {
                    if then_in.is_none() {
                        self.unreachable_branches.push(UnreachableBranch {
                            func: fn_name.to_string(),
                            stmt_id: *id,
                            branch: "then",
                            cond_summary: summarize_expr(cond),
                            reason: format!(
                                "'{}' is unsatisfiable under active path constraints",
                                summarize_expr(cond)
                            ),
                        });
                    } else if !else_body.is_empty() && else_in.is_none() {
                        self.unreachable_branches.push(UnreachableBranch {
                            func: fn_name.to_string(),
                            stmt_id: *id,
                            branch: "else",
                            cond_summary: format!("!({})", summarize_expr(cond)),
                            reason: format!(
                                "'{}' always holds; else branch is unreachable",
                                summarize_expr(cond)
                            ),
                        });
                    }
                }

                let then_out =
                    then_in.and_then(|s| self.analyze_block(fn_name, fn_decl, then_body, s, emit_checks));
                let else_out = if else_body.is_empty() {
                    else_in
                } else {
                    else_in.and_then(|s| self.analyze_block(fn_name, fn_decl, else_body, s, emit_checks))
                };

                match (then_out, else_out) {
                    (Some(a), Some(b)) => Some(a.join(&b)),
                    (Some(a), None) => Some(a),
                    (None, Some(b)) => Some(b),
                    (None, None) => None,
                }
            }
            Stmt::Match { expr, arms, .. } => {
                if emit_checks {
                    self.check_expr_obligations(fn_name, fn_decl, expr, &state);
                }
                let mut joined: Option<SymState> = None;
                let mut rem_state = Some(state);
                for arm in arms {
                    let Some(cur) = rem_state.clone() else {
                        break;
                    };
                    let arm_in = match &arm.pat {
                        MatchPat::Int(v) => {
                            let eq = Expr::Binary {
                                op: BinOp::Eq,
                                left: Box::new(expr.clone()),
                                right: Box::new(Expr::Int(*v)),
                            };
                            rem_state = refine_cond(&eq, false, &cur);
                            refine_cond(&eq, true, &cur)
                        }
                        MatchPat::Wildcard => {
                            rem_state = None;
                            Some(cur)
                        }
                        _ => Some(cur),
                    };
                    if let Some(ain) = arm_in {
                        if let Some(aout) =
                            self.analyze_block(fn_name, fn_decl, &arm.body, ain, emit_checks)
                        {
                            joined = Some(match joined {
                                Some(prev) => prev.join(&aout),
                                None => aout,
                            });
                        }
                    }
                }
                if let Some(rem) = rem_state {
                    joined = Some(match joined {
                        Some(prev) => prev.join(&rem),
                        None => rem,
                    });
                }
                joined
            }
            Stmt::While { cond, body, .. } => {
                let mut inv = state;
                for _ in 0..3 {
                    let body_out = if let Some(in_s) = refine_cond(cond, true, &inv) {
                        self.analyze_block(fn_name, fn_decl, body, in_s, false)
                    } else {
                        None
                    };
                    let stepped = match body_out {
                        Some(bo) => inv.join(&bo),
                        None => inv.clone(),
                    };
                    let next_inv = inv.widen(&stepped);
                    if next_inv == inv {
                        break;
                    }
                    inv = next_inv;
                }
                if emit_checks {
                    self.check_expr_obligations(fn_name, fn_decl, cond, &inv);
                    if let Some(in_s) = refine_cond(cond, true, &inv) {
                        let _ = self.analyze_block(fn_name, fn_decl, body, in_s, true);
                    }
                }
                refine_cond(cond, false, &inv).or(Some(inv))
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                if emit_checks {
                    self.check_expr_obligations(fn_name, fn_decl, start, &state);
                    self.check_expr_obligations(fn_name, fn_decl, end, &state);
                }
                let start_dom = eval_int_domain(start, &state);
                let end_dom = eval_int_domain(end, &state);

                let enter_loop = |s: &SymState| -> Option<SymState> {
                    let s_dom = eval_int_domain(start, s);
                    let e_dom = eval_int_domain(end, s);
                    if s_dom.lo >= e_dom.hi {
                        return None;
                    }
                    let mut inner = s.clone();
                    let hi = e_dom.hi.saturating_sub(1);
                    inner.set_int(var, IntDomain::range(s_dom.lo, hi));
                    if let Some(list_var) = extract_len_target(end, s) {
                        let _ = inner.narrow_len(&list_var, IntDomain::range(s_dom.lo.max(0) + 1, INF));
                        inner.strict_lt_len.insert((var.clone(), list_var));
                    }
                    Some(inner)
                };

                let mut inv = state.clone();
                for _ in 0..3 {
                    let body_out = enter_loop(&inv)
                        .and_then(|in_s| self.analyze_block(fn_name, fn_decl, body, in_s, false));
                    let stepped = match body_out {
                        Some(bo) => inv.join(&bo),
                        None => inv.clone(),
                    };
                    let next_inv = inv.widen(&stepped);
                    if next_inv == inv {
                        break;
                    }
                    inv = next_inv;
                }

                if emit_checks {
                    if let Some(in_s) = enter_loop(&inv) {
                        let _ = self.analyze_block(fn_name, fn_decl, body, in_s, true);
                    }
                }

                let _ = (start_dom, end_dom);
                Some(inv)
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                if emit_checks {
                    self.check_expr_obligations(fn_name, fn_decl, iter, &state);
                }
                let enter_each = |s: &SymState| -> SymState {
                    let mut inner = s.clone();
                    inner.set_int(var, IntDomain::top());
                    if let Expr::Var(lv) = iter {
                        let _ = inner.narrow_len(lv, IntDomain::range(1, INF));
                    }
                    inner
                };

                let mut inv = state;
                for _ in 0..3 {
                    let in_s = enter_each(&inv);
                    let body_out = self.analyze_block(fn_name, fn_decl, body, in_s, false);
                    let stepped = match body_out {
                        Some(bo) => inv.join(&bo),
                        None => inv.clone(),
                    };
                    let next_inv = inv.widen(&stepped);
                    if next_inv == inv {
                        break;
                    }
                    inv = next_inv;
                }

                if emit_checks {
                    let in_s = enter_each(&inv);
                    let _ = self.analyze_block(fn_name, fn_decl, body, in_s, true);
                }
                Some(inv)
            }
            Stmt::Break { .. } | Stmt::Continue { .. } => None,
            Stmt::Return { value, .. } => {
                if emit_checks {
                    if let Some(v) = value {
                        self.check_expr_obligations(fn_name, fn_decl, v, &state);
                    }
                }
                None
            }
            Stmt::Assert { cond, .. } => {
                if emit_checks {
                    self.check_expr_obligations(fn_name, fn_decl, cond, &state);
                    self.check_assertion(fn_name, fn_decl, cond, &state);
                }
                refine_cond(cond, true, &state).or(Some(state))
            }
            Stmt::AssertEq { left, right, .. } => {
                let eq = Expr::Binary {
                    op: BinOp::Eq,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                if emit_checks {
                    self.check_expr_obligations(fn_name, fn_decl, left, &state);
                    self.check_expr_obligations(fn_name, fn_decl, right, &state);
                    self.check_assertion(fn_name, fn_decl, &eq, &state);
                }
                refine_cond(&eq, true, &state).or(Some(state))
            }
            Stmt::Expr { expr, .. } => {
                if emit_checks {
                    self.check_expr_obligations(fn_name, fn_decl, expr, &state);
                }
                if let Expr::Intrinsic(intr) = expr {
                    if let Intrinsic::Push {
                        list: Expr::Var(lv),
                        ..
                    } = intr.as_ref()
                    {
                        let cur = state.len_dom(lv);
                        state.lens.insert(
                            lv.clone(),
                            IntDomain::range(cur.lo.saturating_add(1), cur.hi.saturating_add(1)),
                        );
                    }
                }
                Some(state)
            }
        }
    }

    fn check_expr_obligations(
        &mut self,
        fn_name: &str,
        fn_decl: &FnDecl,
        expr: &Expr,
        state: &SymState,
    ) {
        match expr {
            Expr::Unary { expr: inner, .. } | Expr::FieldAccess { base: inner, .. } => {
                self.check_expr_obligations(fn_name, fn_decl, inner, state);
            }
            Expr::Index { base, index } => {
                self.check_expr_obligations(fn_name, fn_decl, base, state);
                self.check_expr_obligations(fn_name, fn_decl, index, state);
                self.check_index_access(fn_name, fn_decl, base, index, state);
            }
            Expr::Binary { op, left, right } => {
                self.check_expr_obligations(fn_name, fn_decl, left, state);
                if *op == BinOp::And {
                    if let Some(s_rhs) = refine_cond(left, true, state) {
                        self.check_expr_obligations(fn_name, fn_decl, right, &s_rhs);
                    }
                    return;
                }
                if *op == BinOp::Or {
                    if let Some(s_rhs) = refine_cond(left, false, state) {
                        self.check_expr_obligations(fn_name, fn_decl, right, &s_rhs);
                    }
                    return;
                }
                self.check_expr_obligations(fn_name, fn_decl, right, state);

                if matches!(op, BinOp::Div | BinOp::IntDiv | BinOp::Mod)
                    && !expr_is_float(right, fn_decl)
                {
                    self.check_div_by_zero(fn_name, fn_decl, expr, right, state);
                }
            }
            Expr::List(items) | Expr::Call { args: items, .. } => {
                for it in items {
                    self.check_expr_obligations(fn_name, fn_decl, it, state);
                }
            }
            Expr::StructInit { fields, .. } => {
                for (_, v) in fields {
                    self.check_expr_obligations(fn_name, fn_decl, v, state);
                }
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e)
                | Intrinsic::Abs(e)
                | Intrinsic::Upper(e)
                | Intrinsic::Lower(e)
                | Intrinsic::ToStr(e) => {
                    self.check_expr_obligations(fn_name, fn_decl, e, state);
                }
                Intrinsic::Min(a, b)
                | Intrinsic::Max(a, b)
                | Intrinsic::Push { list: a, value: b }
                | Intrinsic::Contains {
                    haystack: a,
                    needle: b,
                } => {
                    self.check_expr_obligations(fn_name, fn_decl, a, state);
                    self.check_expr_obligations(fn_name, fn_decl, b, state);
                }
                Intrinsic::Print(args) => {
                    for a in args {
                        self.check_expr_obligations(fn_name, fn_decl, a, state);
                    }
                }
            },
            _ => {}
        }
    }

    fn check_div_by_zero(
        &mut self,
        fn_name: &str,
        fn_decl: &FnDecl,
        full_expr: &Expr,
        divisor: &Expr,
        state: &SymState,
    ) {
        let id = self.next_obligation_id;
        self.next_obligation_id += 1;
        let div_dom = eval_int_domain(divisor, state);
        let summary = summarize_expr(full_expr);

        if !div_dom.contains(0) {
            self.obligations.push(SafetyObligation {
                id,
                func: fn_name.to_string(),
                kind: ObligationKind::DivByZero,
                expr_summary: summary,
                status: VerifyStatus::ProvenSafe,
                proof_note: format!(
                    "divisor '{}' ∈ {} excludes 0",
                    summarize_expr(divisor),
                    div_dom.display()
                ),
            });
            return;
        }

        if let Some((call_str, err_msg)) =
            self.search_crash_witness(fn_decl, &["division by zero", "modulo by zero"])
        {
            self.obligations.push(SafetyObligation {
                id,
                func: fn_name.to_string(),
                kind: ObligationKind::DivByZero,
                expr_summary: summary,
                status: VerifyStatus::Refuted {
                    witness_call: call_str.clone(),
                    runtime_error: err_msg.clone(),
                },
                proof_note: format!("counterexample `{}` triggers {}", call_str, err_msg),
            });
        } else {
            self.obligations.push(SafetyObligation {
                id,
                func: fn_name.to_string(),
                kind: ObligationKind::DivByZero,
                expr_summary: summary,
                status: VerifyStatus::UnprovenWarning,
                proof_note: format!(
                    "divisor '{}' ∈ {} includes 0 (unproven statically)",
                    summarize_expr(divisor),
                    div_dom.display()
                ),
            });
        }
    }

    fn check_index_access(
        &mut self,
        fn_name: &str,
        fn_decl: &FnDecl,
        base: &Expr,
        index: &Expr,
        state: &SymState,
    ) {
        let id = self.next_obligation_id;
        self.next_obligation_id += 1;
        let idx_dom = eval_int_domain(index, state);
        let summary = format!("{}[{}]", summarize_expr(base), summarize_expr(index));

        let non_neg = idx_dom.lo >= 0;
        let upper_safe = match base {
            Expr::Var(lv) => {
                let ldom = state.len_dom(lv);
                let interval_lt = idx_dom.hi < ldom.lo;
                let rel_lt = match index {
                    Expr::Var(iv) => state.strict_lt_len.contains(&(iv.clone(), lv.clone())),
                    _ => false,
                };
                interval_lt || rel_lt
            }
            Expr::List(items) => idx_dom.hi < items.len() as i64,
            _ => false,
        };

        if non_neg && upper_safe {
            let note = if let (Expr::Var(iv), Expr::Var(lv)) = (index, base) {
                if state.strict_lt_len.contains(&(iv.clone(), lv.clone())) {
                    format!(
                        "0 <= {} (∈ {}) and {} < len({})",
                        iv,
                        idx_dom.display(),
                        iv,
                        lv
                    )
                } else {
                    format!(
                        "index ∈ {} strictly within len({}) ∈ {}",
                        idx_dom.display(),
                        lv,
                        state.len_dom(lv).display()
                    )
                }
            } else {
                format!("index ∈ {} proven in-bounds", idx_dom.display())
            };
            self.obligations.push(SafetyObligation {
                id,
                func: fn_name.to_string(),
                kind: ObligationKind::IndexBounds,
                expr_summary: summary,
                status: VerifyStatus::ProvenSafe,
                proof_note: note,
            });
            return;
        }

        if let Some((call_str, err_msg)) = self.search_crash_witness(fn_decl, &["out of bounds"]) {
            self.obligations.push(SafetyObligation {
                id,
                func: fn_name.to_string(),
                kind: ObligationKind::IndexBounds,
                expr_summary: summary,
                status: VerifyStatus::Refuted {
                    witness_call: call_str.clone(),
                    runtime_error: err_msg.clone(),
                },
                proof_note: format!("counterexample `{}` triggers {}", call_str, err_msg),
            });
        } else {
            self.obligations.push(SafetyObligation {
                id,
                func: fn_name.to_string(),
                kind: ObligationKind::IndexBounds,
                expr_summary: summary,
                status: VerifyStatus::UnprovenWarning,
                proof_note: format!("index ∈ {} could exceed list bounds", idx_dom.display()),
            });
        }
    }

    fn check_assertion(
        &mut self,
        fn_name: &str,
        fn_decl: &FnDecl,
        cond: &Expr,
        state: &SymState,
    ) {
        let id = self.next_obligation_id;
        self.next_obligation_id += 1;
        let summary = format!("assert({})", summarize_expr(cond));

        if refine_cond(cond, false, state).is_none() {
            self.obligations.push(SafetyObligation {
                id,
                func: fn_name.to_string(),
                kind: ObligationKind::Assertion,
                expr_summary: summary,
                status: VerifyStatus::ProvenSafe,
                proof_note: "negation is UNSAT across all reachable path states".to_string(),
            });
            return;
        }

        if let Some((call_str, err_msg)) =
            self.search_crash_witness(fn_decl, &["assertion failed", "assert_eq failed"])
        {
            self.obligations.push(SafetyObligation {
                id,
                func: fn_name.to_string(),
                kind: ObligationKind::Assertion,
                expr_summary: summary,
                status: VerifyStatus::Refuted {
                    witness_call: call_str.clone(),
                    runtime_error: err_msg.clone(),
                },
                proof_note: format!("counterexample `{}` violates contract ({})", call_str, err_msg),
            });
        } else {
            self.obligations.push(SafetyObligation {
                id,
                func: fn_name.to_string(),
                kind: ObligationKind::Assertion,
                expr_summary: summary,
                status: VerifyStatus::UnprovenWarning,
                proof_note: "contract could not be proven by interval invariants alone".to_string(),
            });
        }
    }

    fn search_crash_witness(
        &self,
        fn_decl: &FnDecl,
        err_substrings: &[&str],
    ) -> Option<(String, String)> {
        let candidates = self.build_witness_tuples(fn_decl, 192);
        for args in &candidates {
            if let Err(err) = eval_fn_call(self.hub, &fn_decl.name, args, WITNESS_STEP_BUDGET) {
                if err_substrings.iter().any(|sub| err.contains(sub)) {
                    let arg_strs: Vec<String> = args.iter().map(summarize_expr).collect();
                    let call_str = format!("{}({})", fn_decl.name, arg_strs.join(", "));
                    return Some((call_str, err));
                }
            }
        }
        None
    }

    fn build_witness_tuples(&self, f: &FnDecl, limit: usize) -> Vec<Vec<Expr>> {
        if f.params.is_empty() {
            return vec![Vec::new()];
        }
        let pools: Vec<Vec<Expr>> = f
            .params
            .iter()
            .map(|p| self.probes_for_param(&p.ty))
            .collect();
        if pools.iter().any(|pp| pp.is_empty()) {
            return Vec::new();
        }

        let mut out = Vec::new();
        if pools.len() == 1 {
            for a in pools[0].iter().take(limit) {
                out.push(vec![a.clone()]);
            }
        } else if pools.len() == 2 {
            for a in &pools[0] {
                for b in &pools[1] {
                    out.push(vec![a.clone(), b.clone()]);
                    if out.len() >= limit {
                        return out;
                    }
                }
            }
        } else {
            for step in 0..limit {
                let mut row = Vec::with_capacity(pools.len());
                let mut idx = step;
                for pp in &pools {
                    row.push(pp[idx % pp.len()].clone());
                    idx = (idx / pp.len()).wrapping_add(step + 1);
                }
                if !out.contains(&row) {
                    out.push(row);
                }
            }
        }
        out
    }

    fn probes_for_param(&self, ty: &Type) -> Vec<Expr> {
        match ty {
            Type::Int => self
                .boundary_ints
                .iter()
                .take(24)
                .map(|&v| {
                    if v < 0 {
                        Expr::Unary {
                            op: UnaryOp::Neg,
                            expr: Box::new(Expr::Int(-v)),
                        }
                    } else {
                        Expr::Int(v)
                    }
                })
                .collect(),
            Type::Float => vec![
                Expr::Float(0.0),
                Expr::Float(1.0),
                Expr::Unary {
                    op: UnaryOp::Neg,
                    expr: Box::new(Expr::Float(1.0)),
                },
            ],
            Type::Bool => vec![Expr::Bool(false), Expr::Bool(true)],
            Type::Str => vec![
                Expr::Str(String::new()),
                Expr::Str("a".to_string()),
                Expr::Str("test".to_string()),
            ],
            Type::Void => Vec::new(),
            Type::Named(name) => {
                if let Some(en) = self.hub.find_enum(name) {
                    en.variants
                        .iter()
                        .map(|v| Expr::EnumVariant {
                            enum_name: name.clone(),
                            variant: v.clone(),
                        })
                        .collect()
                } else if let Some(st) = self.hub.find_struct(name) {
                    let fpools: Vec<(String, Vec<Expr>)> = st
                        .fields
                        .iter()
                        .map(|fl| (fl.name.clone(), self.probes_for_param(&fl.ty)))
                        .collect();
                    if fpools.iter().any(|(_, fp)| fp.is_empty()) && !st.fields.is_empty() {
                        return Vec::new();
                    }
                    let mut structs = Vec::new();
                    for k in 0..3 {
                        let fields = fpools
                            .iter()
                            .map(|(fnm, fp)| (fnm.clone(), fp[k % fp.len()].clone()))
                            .collect();
                        structs.push(Expr::StructInit {
                            name: name.clone(),
                            fields,
                        });
                    }
                    structs
                } else {
                    Vec::new()
                }
            }
            Type::List(inner) => {
                let ep = self.probes_for_param(inner);
                let mut lists = vec![Expr::List(Vec::new())];
                if let Some(e0) = ep.first() {
                    lists.push(Expr::List(vec![e0.clone()]));
                }
                if ep.len() >= 2 {
                    lists.push(Expr::List(vec![ep[0].clone(), ep[1].clone()]));
                }
                lists
            }
        }
    }
}

fn eval_int_domain(expr: &Expr, state: &SymState) -> IntDomain {
    match expr {
        Expr::Int(v) => IntDomain::constant(*v),
        Expr::Var(v) => state.int_dom(v),
        Expr::Unary {
            op: UnaryOp::Neg,
            expr: inner,
        } => {
            let d = eval_int_domain(inner, state);
            if d.is_empty() {
                d
            } else {
                IntDomain::range(-d.hi, -d.lo)
            }
        }
        Expr::Binary { op, left, right } => {
            let l = eval_int_domain(left, state);
            let r = eval_int_domain(right, state);
            if l.is_empty() || r.is_empty() {
                return IntDomain::range(1, 0);
            }
            match op {
                BinOp::Add => add_domains(&l, &r),
                BinOp::Sub => sub_domains(&l, &r),
                BinOp::Mul => mul_domains(&l, &r),
                BinOp::Div | BinOp::IntDiv => div_domains(&l, &r),
                BinOp::Mod => mod_domains(&l, &r),
                _ => IntDomain::top(),
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(Expr::Var(v)) => state.len_dom(v),
            Intrinsic::Len(Expr::List(items)) => IntDomain::constant(items.len() as i64),
            Intrinsic::Len(Expr::Str(s)) => IntDomain::constant(s.len() as i64),
            Intrinsic::Len(_) => IntDomain::non_negative(),
            Intrinsic::Abs(e) => {
                let d = eval_int_domain(e, state);
                if d.is_empty() {
                    d
                } else if d.lo >= 0 {
                    d
                } else if d.hi <= 0 {
                    IntDomain::range(-d.hi, -d.lo)
                } else {
                    IntDomain::range(0, (-d.lo).max(d.hi))
                }
            }
            Intrinsic::Min(a, b) => {
                let da = eval_int_domain(a, state);
                let db = eval_int_domain(b, state);
                IntDomain::range(da.lo.min(db.lo), da.hi.min(db.hi))
            }
            Intrinsic::Max(a, b) => {
                let da = eval_int_domain(a, state);
                let db = eval_int_domain(b, state);
                IntDomain::range(da.lo.max(db.lo), da.hi.max(db.hi))
            }
            _ => IntDomain::top(),
        },
        _ => IntDomain::top(),
    }
}

fn eval_bool_domain(expr: &Expr, state: &SymState) -> Option<BoolDomain> {
    match expr {
        Expr::Bool(b) => Some(BoolDomain::constant(*b)),
        Expr::Var(v) => state.bools.get(v).copied(),
        Expr::Unary {
            op: UnaryOp::Not,
            expr: inner,
        } => eval_bool_domain(inner, state).map(|d| BoolDomain {
            can_false: d.can_true,
            can_true: d.can_false,
        }),
        _ => None,
    }
}

fn add_domains(a: &IntDomain, b: &IntDomain) -> IntDomain {
    let lo = if a.lo <= -INF || b.lo <= -INF {
        -INF
    } else {
        a.lo.saturating_add(b.lo).clamp(-INF, INF)
    };
    let hi = if a.hi >= INF || b.hi >= INF {
        INF
    } else {
        a.hi.saturating_add(b.hi).clamp(-INF, INF)
    };
    IntDomain::range(lo, hi)
}

fn sub_domains(a: &IntDomain, b: &IntDomain) -> IntDomain {
    let lo = if a.lo <= -INF || b.hi >= INF {
        -INF
    } else {
        a.lo.saturating_sub(b.hi).clamp(-INF, INF)
    };
    let hi = if a.hi >= INF || b.lo <= -INF {
        INF
    } else {
        a.hi.saturating_sub(b.lo).clamp(-INF, INF)
    };
    IntDomain::range(lo, hi)
}

fn mul_domains(a: &IntDomain, b: &IntDomain) -> IntDomain {
    if a.lo >= 0 && b.lo >= 0 {
        let lo = a.lo.saturating_mul(b.lo).clamp(0, INF);
        let hi = if a.hi >= INF || b.hi >= INF {
            INF
        } else {
            a.hi.saturating_mul(b.hi).clamp(0, INF)
        };
        return IntDomain::range(lo, hi);
    }
    if a.lo > -INF && a.hi < INF && b.lo > -INF && b.hi < INF {
        let corners = [
            a.lo.saturating_mul(b.lo),
            a.lo.saturating_mul(b.hi),
            a.hi.saturating_mul(b.lo),
            a.hi.saturating_mul(b.hi),
        ];
        let lo = *corners.iter().min().unwrap();
        let hi = *corners.iter().max().unwrap();
        return IntDomain::range(lo, hi);
    }
    IntDomain::top()
}

fn div_domains(a: &IntDomain, b: &IntDomain) -> IntDomain {
    if a.lo >= 0 && b.lo >= 1 {
        let lo = if b.hi >= INF { 0 } else { a.lo / b.hi };
        let hi = if a.hi >= INF { INF } else { a.hi / b.lo };
        return IntDomain::range(lo, hi);
    }
    if b.lo == b.hi && b.lo != 0 && a.lo > -INF && a.hi < INF {
        let c1 = a.lo / b.lo;
        let c2 = a.hi / b.lo;
        return IntDomain::range(c1.min(c2), c1.max(c2));
    }
    IntDomain::top()
}

fn mod_domains(a: &IntDomain, b: &IntDomain) -> IntDomain {
    if b.lo >= 1 && b.hi < INF {
        let max_rem = b.hi - 1;
        if a.lo >= 0 {
            return IntDomain::range(0, max_rem);
        }
        return IntDomain::range(-max_rem, max_rem);
    }
    IntDomain::top()
}

fn extract_len_target(expr: &Expr, state: &SymState) -> Option<String> {
    match expr {
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(Expr::Var(lv)) => Some(lv.clone()),
            _ => None,
        },
        Expr::Var(v) => state.len_aliases.get(v).cloned(),
        _ => None,
    }
}

fn refine_cond(cond: &Expr, truth: bool, state: &SymState) -> Option<SymState> {
    match cond {
        Expr::Bool(b) => {
            if *b == truth {
                Some(state.clone())
            } else {
                None
            }
        }
        Expr::Var(v) => {
            let mut next = state.clone();
            let cur = next.bool_dom(v);
            let narrowed = BoolDomain {
                can_false: cur.can_false && !truth,
                can_true: cur.can_true && truth,
            };
            if narrowed.is_empty() {
                None
            } else {
                next.bools.insert(v.clone(), narrowed);
                Some(next)
            }
        }
        Expr::Unary {
            op: UnaryOp::Not,
            expr: inner,
        } => refine_cond(inner, !truth, state),
        Expr::Binary {
            op: BinOp::And,
            left,
            right,
        } => {
            if truth {
                let s1 = refine_cond(left, true, state)?;
                refine_cond(right, true, &s1)
            } else {
                let a = refine_cond(left, false, state);
                let b = refine_cond(left, true, state)
                    .and_then(|s_true| refine_cond(right, false, &s_true));
                match (a, b) {
                    (Some(sa), Some(sb)) => Some(sa.join(&sb)),
                    (Some(sa), None) => Some(sa),
                    (None, Some(sb)) => Some(sb),
                    (None, None) => None,
                }
            }
        }
        Expr::Binary {
            op: BinOp::Or,
            left,
            right,
        } => {
            if !truth {
                let s1 = refine_cond(left, false, state)?;
                refine_cond(right, false, &s1)
            } else {
                let a = refine_cond(left, true, state);
                let b = refine_cond(left, false, state)
                    .and_then(|s_false| refine_cond(right, true, &s_false));
                match (a, b) {
                    (Some(sa), Some(sb)) => Some(sa.join(&sb)),
                    (Some(sa), None) => Some(sa),
                    (None, Some(sb)) => Some(sb),
                    (None, None) => None,
                }
            }
        }
        Expr::Binary { op, left, right }
            if matches!(
                op,
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
            ) =>
        {
            let eff_op = if truth {
                *op
            } else {
                match op {
                    BinOp::Eq => BinOp::Ne,
                    BinOp::Ne => BinOp::Eq,
                    BinOp::Lt => BinOp::Ge,
                    BinOp::Le => BinOp::Gt,
                    BinOp::Gt => BinOp::Le,
                    BinOp::Ge => BinOp::Lt,
                    other => *other,
                }
            };
            refine_comparison(eff_op, left, right, state)
        }
        _ => Some(state.clone()),
    }
}

fn refine_comparison(
    op: BinOp,
    left: &Expr,
    right: &Expr,
    state: &SymState,
) -> Option<SymState> {
    // Handle boolean / enum literal comparisons (`false == true`)
    if let (Expr::Bool(a), Expr::Bool(b)) = (left, right) {
        let ok = match op {
            BinOp::Eq => a == b,
            BinOp::Ne => a != b,
            _ => true,
        };
        return if ok { Some(state.clone()) } else { None };
    }
    if let (
        Expr::EnumVariant {
            enum_name: e1,
            variant: v1,
        },
        Expr::EnumVariant {
            enum_name: e2,
            variant: v2,
        },
    ) = (left, right)
    {
        if e1 == e2 {
            let ok = match op {
                BinOp::Eq => v1 == v2,
                BinOp::Ne => v1 != v2,
                _ => true,
            };
            return if ok { Some(state.clone()) } else { None };
        }
    }

    // Only apply integer interval check when operands can be integer-typed
    if matches!(
        left,
        Expr::Str(_) | Expr::Bool(_) | Expr::EnumVariant { .. } | Expr::List(_) | Expr::StructInit { .. }
    ) || matches!(
        right,
        Expr::Str(_) | Expr::Bool(_) | Expr::EnumVariant { .. } | Expr::List(_) | Expr::StructInit { .. }
    ) {
        return Some(state.clone());
    }

    let mut next = state.clone();
    let l_dom = eval_int_domain(left, &next);
    let r_dom = eval_int_domain(right, &next);
    if l_dom.is_empty() || r_dom.is_empty() {
        return None;
    }

    // Quick feasibility check on current intervals
    let feasible = match op {
        BinOp::Eq => !l_dom.intersect(&r_dom).is_empty(),
        BinOp::Ne => !(l_dom.lo == l_dom.hi && r_dom.lo == r_dom.hi && l_dom.lo == r_dom.lo),
        BinOp::Lt => l_dom.lo < r_dom.hi,
        BinOp::Le => l_dom.lo <= r_dom.hi,
        BinOp::Gt => l_dom.hi > r_dom.lo,
        BinOp::Ge => l_dom.hi >= r_dom.lo,
        _ => true,
    };
    if !feasible {
        return None;
    }

    // Narrow LHS (`Var(x)` or `Len(Var(xs))`)
    let narrow_target = |target: &Expr, bound: IntDomain, st: &mut SymState| -> bool {
        match target {
            Expr::Var(v) => {
                let merged = st.int_dom(v).intersect(&bound);
                st.narrow_int(v, merged)
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(Expr::Var(lv)) => st.narrow_len(lv, bound),
                _ => true,
            },
            _ => true,
        }
    };

    let l_bound = match op {
        BinOp::Eq => r_dom.clone(),
        BinOp::Ne => {
            let mut d = l_dom.clone();
            if r_dom.lo == r_dom.hi {
                d.exclude(r_dom.lo);
            }
            d
        }
        BinOp::Lt => IntDomain::range(-INF, r_dom.hi.saturating_sub(1)),
        BinOp::Le => IntDomain::range(-INF, r_dom.hi),
        BinOp::Gt => IntDomain::range(r_dom.lo.saturating_add(1), INF),
        BinOp::Ge => IntDomain::range(r_dom.lo, INF),
        _ => IntDomain::top(),
    };
    if !narrow_target(left, l_bound, &mut next) {
        return None;
    }

    let l_after = eval_int_domain(left, &next);
    let r_bound = match op {
        BinOp::Eq => l_after.clone(),
        BinOp::Ne => {
            let mut d = r_dom.clone();
            if l_after.lo == l_after.hi {
                d.exclude(l_after.lo);
            }
            d
        }
        BinOp::Lt => IntDomain::range(l_after.lo.saturating_add(1), INF),
        BinOp::Le => IntDomain::range(l_after.lo, INF),
        BinOp::Gt => IntDomain::range(-INF, l_after.hi.saturating_sub(1)),
        BinOp::Ge => IntDomain::range(-INF, l_after.hi),
        _ => IntDomain::top(),
    };
    if !narrow_target(right, r_bound, &mut next) {
        return None;
    }

    // Record relational upper-bound `idx < len(xs)`!
    if op == BinOp::Lt {
        if let Expr::Var(iv) = left {
            if let Some(lv) = extract_len_target(right, &next) {
                next.strict_lt_len.insert((iv.clone(), lv));
            }
        }
    } else if op == BinOp::Gt {
        if let Expr::Var(iv) = right {
            if let Some(lv) = extract_len_target(left, &next) {
                next.strict_lt_len.insert((iv.clone(), lv));
            }
        }
    }

    Some(next)
}

fn expr_is_float(expr: &Expr, f: &FnDecl) -> bool {
    match expr {
        Expr::Float(_) => true,
        Expr::Var(v) => f
            .params
            .iter()
            .any(|p| p.name == *v && p.ty == Type::Float),
        Expr::Unary { expr: inner, .. } => expr_is_float(inner, f),
        Expr::Binary { left, right, .. } => expr_is_float(left, f) || expr_is_float(right, f),
        _ => false,
    }
}

fn collect_boundary_ints(hub: &HubModule) -> Vec<i64> {
    let mut raw = BTreeSet::new();
    fn visit_stmts(stmts: &[Stmt], out: &mut BTreeSet<i64>) {
        for s in stmts {
            match s {
                Stmt::Let { value, .. } | Stmt::Assign { value, .. } => visit_expr(value, out),
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    visit_expr(cond, out);
                    visit_stmts(then_body, out);
                    visit_stmts(else_body, out);
                }
                Stmt::Match { expr, arms, .. } => {
                    visit_expr(expr, out);
                    for a in arms {
                        visit_stmts(&a.body, out);
                    }
                }
                Stmt::While { cond, body, .. } | Stmt::ForEach { iter: cond, body, .. } => {
                    visit_expr(cond, out);
                    visit_stmts(body, out);
                }
                Stmt::ForRange {
                    start, end, body, ..
                } => {
                    visit_expr(start, out);
                    visit_expr(end, out);
                    visit_stmts(body, out);
                }
                Stmt::Return {
                    value: Some(v), ..
                } => visit_expr(v, out),
                Stmt::Assert { cond, .. } => visit_expr(cond, out),
                Stmt::AssertEq { left, right, .. } => {
                    visit_expr(left, out);
                    visit_expr(right, out);
                }
                Stmt::Expr { expr, .. } => visit_expr(expr, out),
                _ => {}
            }
        }
    }
    fn visit_expr(e: &Expr, out: &mut BTreeSet<i64>) {
        match e {
            Expr::Int(v) => {
                out.insert(*v);
            }
            Expr::Unary {
                op: UnaryOp::Neg,
                expr: inner,
            } => {
                if let Expr::Int(v) = inner.as_ref() {
                    out.insert(-*v);
                }
                visit_expr(inner, out);
            }
            Expr::Unary { expr: inner, .. } | Expr::FieldAccess { base: inner, .. } => {
                visit_expr(inner, out)
            }
            Expr::Binary { left, right, .. }
            | Expr::Index {
                base: left,
                index: right,
            } => {
                visit_expr(left, out);
                visit_expr(right, out);
            }
            Expr::List(xs) | Expr::Call { args: xs, .. } => {
                for x in xs {
                    visit_expr(x, out);
                }
            }
            Expr::StructInit { fields, .. } => {
                for (_, v) in fields {
                    visit_expr(v, out);
                }
            }
            _ => {}
        }
    }

    for item in &hub.items {
        if let Item::Function(f) = item {
            visit_stmts(&f.body, &mut raw);
        }
    }

    let mut ordered = vec![0, -1, 1];
    for c in raw {
        for cand in [c, c.saturating_sub(1), c.saturating_add(1)] {
            if !ordered.contains(&cand) {
                ordered.push(cand);
            }
        }
    }
    for extra in [2, -2, 10, 100] {
        if !ordered.contains(&extra) {
            ordered.push(extra);
        }
    }
    ordered
}

fn summarize_expr(expr: &Expr) -> String {
    match expr {
        Expr::Int(v) => v.to_string(),
        Expr::Float(v) => format!("{}", v),
        Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        Expr::Str(s) => format!("\"{}\"", s),
        Expr::Var(v) => v.clone(),
        Expr::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
        Expr::List(items) => {
            let inner: Vec<String> = items.iter().map(summarize_expr).collect();
            format!("[{}]", inner.join(", "))
        }
        Expr::StructInit { name, fields } => {
            let inner: Vec<String> = fields
                .iter()
                .map(|(k, v)| format!("{}: {}", k, summarize_expr(v)))
                .collect();
            format!("{} {{ {} }}", name, inner.join(", "))
        }
        Expr::FieldAccess { base, field } => format!("{}.{}", summarize_expr(base), field),
        Expr::Index { base, index } => {
            format!("{}[{}]", summarize_expr(base), summarize_expr(index))
        }
        Expr::Unary { op, expr: inner } => {
            let sym = match op {
                UnaryOp::Neg => "-",
                UnaryOp::Not => "!",
            };
            format!("{}{}", sym, summarize_expr(inner))
        }
        Expr::Binary { op, left, right } => {
            let sym = match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "/",
                BinOp::IntDiv => "//",
                BinOp::Mod => "%",
                BinOp::Eq => "==",
                BinOp::Ne => "!=",
                BinOp::Lt => "<",
                BinOp::Le => "<=",
                BinOp::Gt => ">",
                BinOp::Ge => ">=",
                BinOp::And => "&&",
                BinOp::Or => "||",
            };
            format!("{} {} {}", summarize_expr(left), sym, summarize_expr(right))
        }
        Expr::Call { func, args } => {
            let inner: Vec<String> = args.iter().map(summarize_expr).collect();
            format!("{}({})", func, inner.join(", "))
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(e) => format!("len({})", summarize_expr(e)),
            Intrinsic::Abs(e) => format!("abs({})", summarize_expr(e)),
            Intrinsic::Min(a, b) => format!("min({}, {})", summarize_expr(a), summarize_expr(b)),
            Intrinsic::Max(a, b) => format!("max({}, {})", summarize_expr(a), summarize_expr(b)),
            Intrinsic::Upper(e) => format!("upper({})", summarize_expr(e)),
            Intrinsic::Lower(e) => format!("lower({})", summarize_expr(e)),
            Intrinsic::ToStr(e) => format!("str({})", summarize_expr(e)),
            Intrinsic::Contains { haystack, needle } => {
                format!("contains({}, {})", summarize_expr(haystack), summarize_expr(needle))
            }
            Intrinsic::Push { list, value } => {
                format!("push({}, {})", summarize_expr(list), summarize_expr(value))
            }
            Intrinsic::Print(args) => {
                let inner: Vec<String> = args.iter().map(summarize_expr).collect();
                format!("print({})", inner.join(", "))
            }
        },
    }
}

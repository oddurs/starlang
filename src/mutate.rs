use std::collections::BTreeSet;
use std::time::Instant;

use crate::eval::{eval_fn_call, eval_tests, Value};
use crate::hub::{
    AssignOp, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, Metadata, Stmt, TestDecl, Type,
    UnaryOp,
};
use crate::lens::SpokeId;
use crate::reconcile::reconcile_modules;
use crate::typecheck::check_module;

const MAX_MUTANTS_PER_MODULE: usize = 64;
const MUTANT_TEST_STEP_BUDGET: usize = 10_000;
const PROBE_CALL_STEP_BUDGET: usize = 5_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MutantOutcome {
    pub id: usize,
    pub func: String,
    pub description: String,
    pub killed: bool,
    pub killed_by: Option<String>,
}

#[derive(Debug, Clone)]
pub struct MutationReport {
    pub total_mutants: usize,
    pub killed: usize,
    pub survived: usize,
    pub score_pct: u8,
    pub elapsed_ms: u128,
    pub outcomes: Vec<MutantOutcome>,
}

impl MutationReport {
    pub fn survivors(&self) -> Vec<&MutantOutcome> {
        self.outcomes.iter().filter(|m| !m.killed).collect()
    }
}

#[derive(Debug, Clone)]
pub struct HardenReport {
    pub added_assertions: usize,
    pub before: MutationReport,
    pub after: MutationReport,
}

struct CandidateMutant {
    func: String,
    description: String,
    hub: HubModule,
}

/// Generate semantic single-site AST mutants across all non-`main` Hub functions and
/// run the polyglot Hub VM unit test suite against every statically valid mutant.
pub fn mutate_module(hub: &HubModule) -> MutationReport {
    let (report, _) = mutate_with_survivor_hubs(hub);
    report
}

/// Automatically probe AST-derived boundary inputs in the Hub VM to find concrete inputs
/// that distinguish surviving mutants from the original program, synthesizing a polyglot
/// `test_mutation_hardened` unit test projected simultaneously across all 9 languages.
pub fn harden_tests(hub: &HubModule) -> (HubModule, HardenReport) {
    let (before, surviving_candidates) = mutate_with_survivor_hubs(hub);
    if surviving_candidates.is_empty() {
        let after = before.clone();
        return (
            hub.clone(),
            HardenReport {
                added_assertions: 0,
                before,
                after,
            },
        );
    }

    let pools = BoundaryPools::from_hub(hub);
    let mut new_stmts: Vec<Stmt> = Vec::new();
    let mut added_assertions = 0usize;
    let mut killed_mask = vec![false; surviving_candidates.len()];
    let mut empty_list_counter = 0usize;

    // Group surviving mutants by function in declaration order
    for item in &hub.items {
        let Item::Function(f) = item else {
            continue;
        };
        if f.name == "main" || f.ret_ty == Type::Void {
            continue;
        }

        let fn_survivor_indices: Vec<usize> = surviving_candidates
            .iter()
            .enumerate()
            .filter(|(_, c)| c.func == f.name)
            .map(|(i, _)| i)
            .collect();
        if fn_survivor_indices.is_empty() {
            continue;
        }

        let arg_tuples = generate_arg_tuples(f, hub, &pools, 256);
        for &s_idx in &fn_survivor_indices {
            if killed_mask[s_idx] {
                continue;
            }
            let survivor = &surviving_candidates[s_idx];

            for args in &arg_tuples {
                let Ok(orig_val) = eval_fn_call(hub, &f.name, args, PROBE_CALL_STEP_BUDGET) else {
                    continue;
                };
                let diverges = match eval_fn_call(
                    &survivor.hub,
                    &f.name,
                    args,
                    PROBE_CALL_STEP_BUDGET,
                ) {
                    Ok(mut_val) => mut_val != orig_val,
                    Err(_) => true,
                };
                if !diverges {
                    continue;
                }

                let mut setup_stmts: Vec<Stmt> = Vec::new();
                let mut call_args: Vec<Expr> = Vec::with_capacity(args.len());
                for (p_idx, arg) in args.iter().enumerate() {
                    if matches!(arg, Expr::List(items) if items.is_empty()) {
                        empty_list_counter += 1;
                        let aname = format!("empty_arg_{}", empty_list_counter);
                        setup_stmts.push(Stmt::Let {
                            id: 0,
                            name: aname.clone(),
                            mutable: false,
                            ty: Some(f.params[p_idx].ty.clone()),
                            value: Expr::List(Vec::new()),
                            meta: Metadata::new(),
                        });
                        call_args.push(Expr::Var(aname));
                    } else {
                        call_args.push(arg.clone());
                    }
                }

                let call_expr = Expr::Call {
                    func: f.name.clone(),
                    args: call_args,
                };

                let synthesized = match &orig_val {
                    Value::List(items) if items.is_empty() => {
                        empty_list_counter += 1;
                        let vname = format!("expected_empty_{}", empty_list_counter);
                        setup_stmts.push(Stmt::Let {
                            id: 0,
                            name: vname.clone(),
                            mutable: false,
                            ty: Some(f.ret_ty.clone()),
                            value: Expr::List(Vec::new()),
                            meta: Metadata::new(),
                        });
                        setup_stmts.push(Stmt::AssertEq {
                            id: 0,
                            left: call_expr,
                            right: Expr::Var(vname),
                            meta: Metadata::new(),
                        });
                        Some(setup_stmts)
                    }
                    _ => value_to_expr(&orig_val, hub).map(|expected_expr| {
                        setup_stmts.push(Stmt::AssertEq {
                            id: 0,
                            left: call_expr,
                            right: expected_expr,
                            meta: Metadata::new(),
                        });
                        setup_stmts
                    }),
                };

                if let Some(mut stmts) = synthesized {
                    new_stmts.append(&mut stmts);
                    added_assertions += 1;
                    killed_mask[s_idx] = true;

                    // Mark any other surviving mutants in `f` that this exact probe also kills
                    for &other_idx in &fn_survivor_indices {
                        if !killed_mask[other_idx] {
                            let other_div = match eval_fn_call(
                                &surviving_candidates[other_idx].hub,
                                &f.name,
                                args,
                                PROBE_CALL_STEP_BUDGET,
                            ) {
                                Ok(mv) => mv != orig_val,
                                Err(_) => true,
                            };
                            if other_div {
                                killed_mask[other_idx] = true;
                            }
                        }
                    }
                    break;
                }
            }
        }
    }

    if added_assertions == 0 {
        let after = before.clone();
        return (
            hub.clone(),
            HardenReport {
                added_assertions: 0,
                before,
                after,
            },
        );
    }

    let mut next_raw = hub.clone();
    if let Some(existing) = next_raw.items.iter_mut().find_map(|it| match it {
        Item::Test(t) if t.name == "mutation_hardened" => Some(t),
        _ => None,
    }) {
        existing.body.extend(new_stmts);
    } else {
        next_raw.items.push(Item::Test(TestDecl {
            id: 0,
            name: "mutation_hardened".to_string(),
            body: new_stmts,
            comments: vec![
                "Auto-synthesized boundary assertions killing surviving Hub AST mutants".to_string(),
            ],
            meta: Metadata::new(),
        }));
    }

    let hardened = reconcile_modules(next_raw, hub, SpokeId::Star);
    if !check_module(&hardened).is_empty() {
        let after = before.clone();
        return (
            hub.clone(),
            HardenReport {
                added_assertions: 0,
                before,
                after,
            },
        );
    }

    let after = mutate_module(&hardened);
    (
        hardened,
        HardenReport {
            added_assertions,
            before,
            after,
        },
    )
}

fn mutate_with_survivor_hubs(hub: &HubModule) -> (MutationReport, Vec<CandidateMutant>) {
    let start = Instant::now();
    let candidates = generate_module_mutants(hub);

    let mut outcomes = Vec::with_capacity(candidates.len());
    let mut survivors = Vec::new();
    let mut killed_count = 0usize;

    for (idx, cand) in candidates.into_iter().enumerate() {
        let results = eval_tests(&cand.hub, MUTANT_TEST_STEP_BUDGET);
        let killer = results
            .iter()
            .find(|tr| !tr.passed)
            .map(|tr| format!("test_{}", tr.name));
        let killed = killer.is_some();
        if killed {
            killed_count += 1;
        }
        outcomes.push(MutantOutcome {
            id: idx + 1,
            func: cand.func.clone(),
            description: cand.description.clone(),
            killed,
            killed_by: killer,
        });
        if !killed {
            survivors.push(cand);
        }
    }

    let total_mutants = outcomes.len();
    let survived = total_mutants - killed_count;
    let score_pct = (killed_count * 100)
        .checked_div(total_mutants)
        .unwrap_or(100) as u8;

    let report = MutationReport {
        total_mutants,
        killed: killed_count,
        survived,
        score_pct,
        elapsed_ms: start.elapsed().as_millis(),
        outcomes,
    };
    (report, survivors)
}

// ============================================================================
// Deterministic Single-Site Semantic Mutant Generator
// ============================================================================

#[derive(Clone)]
struct MutationSpec {
    site: usize,
    variant: usize,
    description: String,
}

fn generate_module_mutants(hub: &HubModule) -> Vec<CandidateMutant> {
    let mut out = Vec::new();

    for (item_idx, item) in hub.items.iter().enumerate() {
        let Item::Function(f) = item else {
            continue;
        };
        if f.name == "main" {
            continue;
        }

        let mut specs = Vec::new();
        let mut site_counter = 0usize;
        collect_stmt_specs(&f.body, &mut site_counter, &mut specs);

        for spec in specs {
            if out.len() >= MAX_MUTANTS_PER_MODULE {
                return out;
            }
            let mut mutated_hub = hub.clone();
            if let Item::Function(mf) = &mut mutated_hub.items[item_idx] {
                let mut cur_site = 0usize;
                apply_stmt_mutation(&mut mf.body, &mut cur_site, spec.site, spec.variant);
            }
            if check_module(&mutated_hub).is_empty() {
                out.push(CandidateMutant {
                    func: f.name.clone(),
                    description: spec.description,
                    hub: mutated_hub,
                });
            }
        }
    }

    out
}

fn binop_mutations(op: BinOp) -> Vec<(BinOp, &'static str)> {
    match op {
        BinOp::Lt => vec![(BinOp::Le, "< -> <="), (BinOp::Ge, "< -> >=")],
        BinOp::Le => vec![(BinOp::Lt, "<= -> <"), (BinOp::Gt, "<= -> >")],
        BinOp::Gt => vec![(BinOp::Ge, "> -> >="), (BinOp::Lt, "> -> <")],
        BinOp::Ge => vec![(BinOp::Gt, ">= -> >"), (BinOp::Lt, ">= -> <")],
        BinOp::Eq => vec![(BinOp::Ne, "== -> !=")],
        BinOp::Ne => vec![(BinOp::Eq, "!= -> ==")],
        BinOp::And => vec![(BinOp::Or, "&& -> ||")],
        BinOp::Or => vec![(BinOp::And, "|| -> &&")],
        BinOp::Add => vec![(BinOp::Sub, "+ -> -")],
        BinOp::Sub => vec![(BinOp::Add, "- -> +")],
        BinOp::Mul => vec![(BinOp::Add, "* -> +")],
        BinOp::Div | BinOp::IntDiv | BinOp::Mod => Vec::new(),
    }
}

fn assign_mutations(op: AssignOp) -> Vec<(AssignOp, &'static str)> {
    match op {
        AssignOp::AddAssign => vec![(AssignOp::SubAssign, "+= -> -=")],
        AssignOp::SubAssign => vec![(AssignOp::AddAssign, "-= -> +=")],
        AssignOp::Set => Vec::new(),
    }
}

fn collect_stmt_specs(stmts: &[Stmt], site: &mut usize, out: &mut Vec<MutationSpec>) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { value, .. } => collect_expr_specs(value, site, out),
            Stmt::Assign { op, value, .. } => {
                let muts = assign_mutations(*op);
                if !muts.is_empty() {
                    let s = *site;
                    *site += 1;
                    for (v_idx, (_, desc)) in muts.iter().enumerate() {
                        out.push(MutationSpec {
                            site: s,
                            variant: v_idx,
                            description: (*desc).to_string(),
                        });
                    }
                }
                collect_expr_specs(value, site, out);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                collect_expr_specs(cond, site, out);
                collect_stmt_specs(then_body, site, out);
                collect_stmt_specs(else_body, site, out);
            }
            Stmt::Match { expr, arms, .. } => {
                collect_expr_specs(expr, site, out);
                for arm in arms {
                    collect_stmt_specs(&arm.body, site, out);
                }
            }
            Stmt::While { cond, body, .. } => {
                collect_expr_specs(cond, site, out);
                collect_stmt_specs(body, site, out);
            }
            Stmt::ForEach { iter, body, .. } => {
                collect_expr_specs(iter, site, out);
                collect_stmt_specs(body, site, out);
            }
            Stmt::ForRange {
                start, end, body, ..
            } => {
                collect_expr_specs(start, site, out);
                collect_expr_specs(end, site, out);
                collect_stmt_specs(body, site, out);
            }
            Stmt::Return {
                value: Some(v), ..
            } => collect_expr_specs(v, site, out),
            Stmt::Assert { cond, .. } => collect_expr_specs(cond, site, out),
            Stmt::AssertEq { left, right, .. } => {
                collect_expr_specs(left, site, out);
                collect_expr_specs(right, site, out);
            }
            Stmt::Expr { expr, .. } => collect_expr_specs(expr, site, out),
            Stmt::Return { value: None, .. }
            | Stmt::Break { .. }
            | Stmt::Continue { .. }
            | Stmt::Comment { .. } => {}
        }
    }
}

fn collect_expr_specs(expr: &Expr, site: &mut usize, out: &mut Vec<MutationSpec>) {
    match expr {
        Expr::Binary { op, left, right } => {
            let muts = binop_mutations(*op);
            if !muts.is_empty() {
                let s = *site;
                *site += 1;
                for (v_idx, (_, desc)) in muts.iter().enumerate() {
                    out.push(MutationSpec {
                        site: s,
                        variant: v_idx,
                        description: (*desc).to_string(),
                    });
                }
            }
            collect_expr_specs(left, site, out);
            collect_expr_specs(right, site, out);
        }
        Expr::Unary { expr: inner, .. } => collect_expr_specs(inner, site, out),
        Expr::List(items) => {
            for it in items {
                collect_expr_specs(it, site, out);
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, v) in fields {
                collect_expr_specs(v, site, out);
            }
        }
        Expr::FieldAccess { base, .. } => collect_expr_specs(base, site, out),
        Expr::Index { base, index } => {
            collect_expr_specs(base, site, out);
            collect_expr_specs(index, site, out);
        }
        Expr::Call { args, .. } => {
            for a in args {
                collect_expr_specs(a, site, out);
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(e)
            | Intrinsic::Abs(e)
            | Intrinsic::Upper(e)
            | Intrinsic::Lower(e)
            | Intrinsic::ToStr(e) => collect_expr_specs(e, site, out),
            Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                collect_expr_specs(a, site, out);
                collect_expr_specs(b, site, out);
            }
            Intrinsic::Push { list, value } => {
                collect_expr_specs(list, site, out);
                collect_expr_specs(value, site, out);
            }
            Intrinsic::Print(args) => {
                for a in args {
                    collect_expr_specs(a, site, out);
                }
            }
            Intrinsic::Contains { haystack, needle } => {
                collect_expr_specs(haystack, site, out);
                collect_expr_specs(needle, site, out);
            }
        },
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Bool(_)
        | Expr::Str(_)
        | Expr::Var(_)
        | Expr::EnumVariant { .. } => {}
    }
}

fn apply_stmt_mutation(stmts: &mut [Stmt], site: &mut usize, target: usize, variant: usize) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { value, .. } => apply_expr_mutation(value, site, target, variant),
            Stmt::Assign { op, value, .. } => {
                let muts = assign_mutations(*op);
                if !muts.is_empty() {
                    if *site == target {
                        if let Some((new_op, _)) = muts.get(variant) {
                            *op = *new_op;
                        }
                    }
                    *site += 1;
                }
                apply_expr_mutation(value, site, target, variant);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                apply_expr_mutation(cond, site, target, variant);
                apply_stmt_mutation(then_body, site, target, variant);
                apply_stmt_mutation(else_body, site, target, variant);
            }
            Stmt::Match { expr, arms, .. } => {
                apply_expr_mutation(expr, site, target, variant);
                for arm in arms {
                    apply_stmt_mutation(&mut arm.body, site, target, variant);
                }
            }
            Stmt::While { cond, body, .. } => {
                apply_expr_mutation(cond, site, target, variant);
                apply_stmt_mutation(body, site, target, variant);
            }
            Stmt::ForEach { iter, body, .. } => {
                apply_expr_mutation(iter, site, target, variant);
                apply_stmt_mutation(body, site, target, variant);
            }
            Stmt::ForRange {
                start, end, body, ..
            } => {
                apply_expr_mutation(start, site, target, variant);
                apply_expr_mutation(end, site, target, variant);
                apply_stmt_mutation(body, site, target, variant);
            }
            Stmt::Return {
                value: Some(v), ..
            } => apply_expr_mutation(v, site, target, variant),
            Stmt::Assert { cond, .. } => apply_expr_mutation(cond, site, target, variant),
            Stmt::AssertEq { left, right, .. } => {
                apply_expr_mutation(left, site, target, variant);
                apply_expr_mutation(right, site, target, variant);
            }
            Stmt::Expr { expr, .. } => apply_expr_mutation(expr, site, target, variant),
            Stmt::Return { value: None, .. }
            | Stmt::Break { .. }
            | Stmt::Continue { .. }
            | Stmt::Comment { .. } => {}
        }
    }
}

fn apply_expr_mutation(expr: &mut Expr, site: &mut usize, target: usize, variant: usize) {
    match expr {
        Expr::Binary { op, left, right } => {
            let muts = binop_mutations(*op);
            if !muts.is_empty() {
                if *site == target {
                    if let Some((new_op, _)) = muts.get(variant) {
                        *op = *new_op;
                    }
                }
                *site += 1;
            }
            apply_expr_mutation(left, site, target, variant);
            apply_expr_mutation(right, site, target, variant);
        }
        Expr::Unary { expr: inner, .. } => apply_expr_mutation(inner, site, target, variant),
        Expr::List(items) => {
            for it in items {
                apply_expr_mutation(it, site, target, variant);
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, v) in fields {
                apply_expr_mutation(v, site, target, variant);
            }
        }
        Expr::FieldAccess { base, .. } => apply_expr_mutation(base, site, target, variant),
        Expr::Index { base, index } => {
            apply_expr_mutation(base, site, target, variant);
            apply_expr_mutation(index, site, target, variant);
        }
        Expr::Call { args, .. } => {
            for a in args {
                apply_expr_mutation(a, site, target, variant);
            }
        }
        Expr::Intrinsic(intr) => match intr.as_mut() {
            Intrinsic::Len(e)
            | Intrinsic::Abs(e)
            | Intrinsic::Upper(e)
            | Intrinsic::Lower(e)
            | Intrinsic::ToStr(e) => apply_expr_mutation(e, site, target, variant),
            Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                apply_expr_mutation(a, site, target, variant);
                apply_expr_mutation(b, site, target, variant);
            }
            Intrinsic::Push { list, value } => {
                apply_expr_mutation(list, site, target, variant);
                apply_expr_mutation(value, site, target, variant);
            }
            Intrinsic::Print(args) => {
                for a in args {
                    apply_expr_mutation(a, site, target, variant);
                }
            }
            Intrinsic::Contains { haystack, needle } => {
                apply_expr_mutation(haystack, site, target, variant);
                apply_expr_mutation(needle, site, target, variant);
            }
        },
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Bool(_)
        | Expr::Str(_)
        | Expr::Var(_)
        | Expr::EnumVariant { .. } => {}
    }
}

// ============================================================================
// AST-Guided Boundary Probe Synthesizer
// ============================================================================

struct BoundaryPools {
    ints: Vec<i64>,
    floats: Vec<f64>,
    strs: Vec<String>,
}

impl BoundaryPools {
    fn from_hub(hub: &HubModule) -> Self {
        let mut ast_ints = BTreeSet::new();
        let mut floats = Vec::new();
        let mut strs = BTreeSet::new();

        for item in &hub.items {
            match item {
                Item::Function(f) => harvest_stmts(&f.body, &mut ast_ints, &mut floats, &mut strs),
                Item::Test(t) => harvest_stmts(&t.body, &mut ast_ints, &mut floats, &mut strs),
                _ => {}
            }
        }

        let mut ints = Vec::new();
        // Prioritize exact AST literal boundaries (`c`, `c - 1`, `c + 1`) first!
        for c in ast_ints {
            for candidate in [c, c.saturating_sub(1), c.saturating_add(1)] {
                if !ints.contains(&candidate) {
                    ints.push(candidate);
                }
            }
        }
        for fallback in [0, 1, -1, 2, 5, 10, 50, 100] {
            if !ints.contains(&fallback) {
                ints.push(fallback);
            }
        }

        for f in [0.0, 1.0, -1.0, 2.5] {
            if !floats.iter().any(|x| (*x - f).abs() < 1e-9) {
                floats.push(f);
            }
        }

        let mut str_vec: Vec<String> = strs.into_iter().collect();
        for s in ["", "a", "rust"] {
            let st = s.to_string();
            if !str_vec.contains(&st) {
                str_vec.push(st);
            }
        }

        Self {
            ints,
            floats,
            strs: str_vec,
        }
    }
}

fn harvest_stmts(
    stmts: &[Stmt],
    ints: &mut BTreeSet<i64>,
    floats: &mut Vec<f64>,
    strs: &mut BTreeSet<String>,
) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { value, .. } | Stmt::Assign { value, .. } => {
                harvest_expr(value, ints, floats, strs);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                harvest_expr(cond, ints, floats, strs);
                harvest_stmts(then_body, ints, floats, strs);
                harvest_stmts(else_body, ints, floats, strs);
            }
            Stmt::Match { expr, arms, .. } => {
                harvest_expr(expr, ints, floats, strs);
                for arm in arms {
                    harvest_stmts(&arm.body, ints, floats, strs);
                }
            }
            Stmt::While { cond, body, .. } => {
                harvest_expr(cond, ints, floats, strs);
                harvest_stmts(body, ints, floats, strs);
            }
            Stmt::ForEach { iter, body, .. } => {
                harvest_expr(iter, ints, floats, strs);
                harvest_stmts(body, ints, floats, strs);
            }
            Stmt::ForRange {
                start, end, body, ..
            } => {
                harvest_expr(start, ints, floats, strs);
                harvest_expr(end, ints, floats, strs);
                harvest_stmts(body, ints, floats, strs);
            }
            Stmt::Return {
                value: Some(v), ..
            } => harvest_expr(v, ints, floats, strs),
            Stmt::Assert { cond, .. } => harvest_expr(cond, ints, floats, strs),
            Stmt::AssertEq { left, right, .. } => {
                harvest_expr(left, ints, floats, strs);
                harvest_expr(right, ints, floats, strs);
            }
            Stmt::Expr { expr, .. } => harvest_expr(expr, ints, floats, strs),
            _ => {}
        }
    }
}

fn harvest_expr(
    expr: &Expr,
    ints: &mut BTreeSet<i64>,
    floats: &mut Vec<f64>,
    strs: &mut BTreeSet<String>,
) {
    match expr {
        Expr::Int(v) => {
            ints.insert(*v);
        }
        Expr::Float(v) => {
            for cand in [*v, *v - 1.0, *v + 1.0] {
                if !floats.iter().any(|x| (*x - cand).abs() < 1e-9) {
                    floats.push(cand);
                }
            }
        }
        Expr::Str(s) => {
            strs.insert(s.clone());
            strs.insert(s.to_uppercase());
            strs.insert(s.to_lowercase());
        }
        Expr::Unary {
            op: UnaryOp::Neg,
            expr: inner,
        } => {
            if let Expr::Int(v) = inner.as_ref() {
                ints.insert(-*v);
            }
            harvest_expr(inner, ints, floats, strs);
        }
        Expr::Unary { expr: inner, .. } | Expr::FieldAccess { base: inner, .. } => {
            harvest_expr(inner, ints, floats, strs);
        }
        Expr::Binary { left, right, .. }
        | Expr::Index {
            base: left,
            index: right,
        } => {
            harvest_expr(left, ints, floats, strs);
            harvest_expr(right, ints, floats, strs);
        }
        Expr::List(items) | Expr::Call { args: items, .. } => {
            for it in items {
                harvest_expr(it, ints, floats, strs);
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, v) in fields {
                harvest_expr(v, ints, floats, strs);
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(e)
            | Intrinsic::Abs(e)
            | Intrinsic::Upper(e)
            | Intrinsic::Lower(e)
            | Intrinsic::ToStr(e) => harvest_expr(e, ints, floats, strs),
            Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                harvest_expr(a, ints, floats, strs);
                harvest_expr(b, ints, floats, strs);
            }
            Intrinsic::Push { list, value } => {
                harvest_expr(list, ints, floats, strs);
                harvest_expr(value, ints, floats, strs);
            }
            Intrinsic::Print(args) => {
                for a in args {
                    harvest_expr(a, ints, floats, strs);
                }
            }
            Intrinsic::Contains { haystack, needle } => {
                harvest_expr(haystack, ints, floats, strs);
                harvest_expr(needle, ints, floats, strs);
            }
        },
        Expr::Bool(_) | Expr::Var(_) | Expr::EnumVariant { .. } => {}
    }
}

fn probes_for_type(ty: &Type, hub: &HubModule, pools: &BoundaryPools) -> Vec<Expr> {
    match ty {
        Type::Int => pools
            .ints
            .iter()
            .take(64)
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
        Type::Float => pools
            .floats
            .iter()
            .take(8)
            .map(|&v| {
                if v < 0.0 {
                    Expr::Unary {
                        op: UnaryOp::Neg,
                        expr: Box::new(Expr::Float(-v)),
                    }
                } else {
                    Expr::Float(v)
                }
            })
            .collect(),
        Type::Bool => vec![Expr::Bool(false), Expr::Bool(true)],
        Type::Str => pools.strs.iter().take(8).cloned().map(Expr::Str).collect(),
        Type::Void => Vec::new(),
        Type::Named(name) => {
            if let Some(edecl) = hub.find_enum(name) {
                edecl
                    .variants
                    .iter()
                    .map(|v| Expr::EnumVariant {
                        enum_name: name.clone(),
                        variant: v.clone(),
                    })
                    .collect()
            } else if let Some(sdecl) = hub.find_struct(name) {
                let field_pools: Vec<(String, Vec<Expr>)> = sdecl
                    .fields
                    .iter()
                    .map(|f| (f.name.clone(), probes_for_type(&f.ty, hub, pools)))
                    .collect();
                if field_pools.iter().any(|(_, fp)| fp.is_empty()) && !sdecl.fields.is_empty() {
                    return Vec::new();
                }
                let mut out = Vec::new();
                for k in 0..3 {
                    let fields = field_pools
                        .iter()
                        .map(|(fname, fp)| (fname.clone(), fp[k % fp.len()].clone()))
                        .collect();
                    out.push(Expr::StructInit {
                        name: name.clone(),
                        fields,
                    });
                }
                out
            } else {
                Vec::new()
            }
        }
        Type::List(inner) => {
            // Empty list (lifted to a typed `let` binding) + non-empty boundary lists!
            let elem_probes = probes_for_type(inner, hub, pools);
            let mut lists = vec![Expr::List(Vec::new())];
            if let Some(p0) = elem_probes.first() {
                lists.push(Expr::List(vec![p0.clone()]));
            }
            if elem_probes.len() >= 2 {
                lists.push(Expr::List(vec![
                    elem_probes[0].clone(),
                    elem_probes[1].clone(),
                ]));
                lists.push(Expr::List(vec![
                    elem_probes[1].clone(),
                    elem_probes[0].clone(),
                ]));
            }
            if elem_probes.len() >= 4 {
                lists.push(Expr::List(vec![
                    elem_probes[0].clone(),
                    elem_probes[2].clone(),
                    elem_probes[3].clone(),
                ]));
            }
            lists
        }
    }
}

fn generate_arg_tuples(
    f: &FnDecl,
    hub: &HubModule,
    pools: &BoundaryPools,
    limit: usize,
) -> Vec<Vec<Expr>> {
    if f.params.is_empty() {
        return vec![Vec::new()];
    }
    let param_probes: Vec<Vec<Expr>> = f
        .params
        .iter()
        .map(|p| probes_for_type(&p.ty, hub, pools))
        .collect();
    if param_probes.iter().any(|pp| pp.is_empty()) {
        return Vec::new();
    }

    let mut tuples = Vec::new();
    if param_probes.len() == 1 {
        for a in param_probes[0].iter().take(limit) {
            tuples.push(vec![a.clone()]);
        }
    } else if param_probes.len() == 2 {
        for a in &param_probes[0] {
            for b in &param_probes[1] {
                tuples.push(vec![a.clone(), b.clone()]);
                if tuples.len() >= limit {
                    return tuples;
                }
            }
        }
    } else {
        for step in 0..limit {
            let mut row = Vec::with_capacity(param_probes.len());
            let mut idx = step;
            for pp in &param_probes {
                row.push(pp[idx % pp.len()].clone());
                idx = (idx / pp.len()).wrapping_add(step + 1);
            }
            if !tuples.contains(&row) {
                tuples.push(row);
            }
        }
    }
    tuples
}

fn value_to_expr(val: &Value, hub: &HubModule) -> Option<Expr> {
    match val {
        Value::Int(v) => {
            if *v == i64::MIN {
                None
            } else if *v < 0 {
                Some(Expr::Unary {
                    op: UnaryOp::Neg,
                    expr: Box::new(Expr::Int(-*v)),
                })
            } else {
                Some(Expr::Int(*v))
            }
        }
        Value::Float(v) => {
            if !v.is_finite() {
                None
            } else if *v < 0.0 {
                Some(Expr::Unary {
                    op: UnaryOp::Neg,
                    expr: Box::new(Expr::Float(-*v)),
                })
            } else {
                Some(Expr::Float(*v))
            }
        }
        Value::Bool(b) => Some(Expr::Bool(*b)),
        Value::Str(s) => Some(Expr::Str(s.clone())),
        Value::EnumVariant { enum_name, variant } => Some(Expr::EnumVariant {
            enum_name: enum_name.clone(),
            variant: variant.clone(),
        }),
        Value::List(items) => {
            if items.is_empty() {
                return None;
            }
            let mut exprs = Vec::with_capacity(items.len());
            for it in items {
                exprs.push(value_to_expr(it, hub)?);
            }
            Some(Expr::List(exprs))
        }
        Value::Struct { name, fields } => {
            let sdecl = hub.find_struct(name)?;
            let mut out_fields = Vec::with_capacity(sdecl.fields.len());
            for f in &sdecl.fields {
                let fv = fields.get(&f.name)?;
                out_fields.push((f.name.clone(), value_to_expr(fv, hub)?));
            }
            Some(Expr::StructInit {
                name: name.clone(),
                fields: out_fields,
            })
        }
        Value::Void => None,
    }
}

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::time::Instant;

use crate::complexity::collect_seed_call_args;
use crate::debugger::{compute_stmt_spoke_lines, record_time_travel_default};
use crate::eval::{eval_fn_with_values, eval_tests_default, Value};
use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, MatchPat, NodeId,
    Stmt, UnaryOp,
};
use crate::lens::SpokeId;
use crate::quickcheck::{
    format_repro_across_spokes, run_quickcheck, shrink_failing_call, shrink_value_candidates,
    MinimizedCounterexample,
};
use crate::spokes::lens_for;
use crate::typecheck::check_module;
use crate::verify::verify_module;

#[derive(Debug, Clone)]
pub struct FaultLocation {
    pub stmt_id: NodeId,
    pub func: String,
    pub symptom: String,
    pub spoke_lines: BTreeMap<String, usize>,
}

#[derive(Debug, Clone)]
pub struct SynthesizedPatch {
    pub stmt_id: NodeId,
    pub func: String,
    pub kind: String,
    pub before_summary: String,
    pub after_summary: String,
    pub spoke_lines: BTreeMap<String, usize>,
    pub diffs_by_spoke: BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct RepairReport {
    pub already_healthy: bool,
    pub repaired: bool,
    pub candidates_evaluated: usize,
    pub tests_passed_before: usize,
    pub tests_total: usize,
    pub tests_passed_after: usize,
    pub safety_refuted_before: usize,
    pub safety_refuted_after: usize,
    pub quickcheck_passed: bool,
    pub elapsed_ms: u128,
    pub faults: Vec<FaultLocation>,
    pub patch: Option<SynthesizedPatch>,
    pub repaired_hub: HubModule,
}

#[derive(Debug, Clone)]
pub struct FunctionEquivalence {
    pub name: String,
    pub signature: String,
    pub alpha_equivalent: bool,
    pub bisimulation_trials: usize,
    pub equivalent: bool,
    pub distinguishing_counterexample: Option<MinimizedCounterexample>,
}

#[derive(Debug, Clone)]
pub struct EquivalenceReport {
    pub all_equivalent: bool,
    pub shared_functions: usize,
    pub alpha_identical_count: usize,
    pub total_trials: usize,
    pub elapsed_ms: u128,
    pub functions: Vec<FunctionEquivalence>,
}

/// Localize failing unit tests or refuted symbolic safety obligations and synthesize a minimal,
/// 4-gate verified AST patch across all 13 spoke languages.
pub fn repair_module(hub: &HubModule) -> RepairReport {
    let start = Instant::now();
    let mut numbered = hub.clone();
    ensure_repair_stmt_ids(&mut numbered);

    let initial_tests = eval_tests_default(&numbered);
    let tests_total = initial_tests.len();
    let tests_passed_before = initial_tests.iter().filter(|t| t.passed).count();
    let initial_ver = verify_module(&numbered);
    let safety_refuted_before = initial_ver.refuted;

    if tests_passed_before == tests_total && safety_refuted_before == 0 {
        return RepairReport {
            already_healthy: true,
            repaired: true,
            candidates_evaluated: 0,
            tests_passed_before,
            tests_total,
            tests_passed_after: tests_passed_before,
            safety_refuted_before: 0,
            safety_refuted_after: 0,
            quickcheck_passed: true,
            elapsed_ms: start.elapsed().as_millis(),
            faults: Vec::new(),
            patch: None,
            repaired_hub: numbered,
        };
    }

    let stmt_spoke_lines = compute_stmt_spoke_lines(&numbered);
    let (faults, priority_stmt_ids) =
        localize_faults(&numbered, &initial_tests, &initial_ver, &stmt_spoke_lines);

    let candidates = generate_repair_candidates(&numbered, &priority_stmt_ids);
    let mut candidates_evaluated = 0usize;

    for cand in candidates {
        candidates_evaluated += 1;

        // Gate 1: Static Hub Typecheck
        if !check_module(&cand.patched_hub).is_empty() {
            continue;
        }

        // Gate 2: All Polyglot Unit Tests Pass
        let cand_tests = eval_tests_default(&cand.patched_hub);
        let cand_passed = cand_tests.iter().filter(|t| t.passed).count();
        if cand_passed < cand_tests.len() {
            continue;
        }

        // Gate 3: Symbolic Safety Verifier (0 refuted obligations)
        let cand_ver = verify_module(&cand.patched_hub);
        if cand_ver.refuted > 0 {
            continue;
        }

        // Gate 4: Property-Based QuickCheck
        let qc = run_quickcheck(&cand.patched_hub, 20, 0x57A4_2026_1200);
        if !qc.all_passed {
            continue;
        }

        let mut patched_hub = cand.patched_hub;
        crate::hub::normalize_module(&mut patched_hub);

        let spoke_lines = stmt_spoke_lines
            .get(&cand.stmt_id)
            .cloned()
            .unwrap_or_default();
        let diffs_by_spoke = compute_spoke_patch_diffs(&numbered, &patched_hub);

        let patch = SynthesizedPatch {
            stmt_id: cand.stmt_id,
            func: cand.func,
            kind: cand.kind,
            before_summary: cand.before_summary,
            after_summary: cand.after_summary,
            spoke_lines,
            diffs_by_spoke,
        };

        return RepairReport {
            already_healthy: false,
            repaired: true,
            candidates_evaluated,
            tests_passed_before,
            tests_total,
            tests_passed_after: cand_passed,
            safety_refuted_before,
            safety_refuted_after: cand_ver.refuted,
            quickcheck_passed: true,
            elapsed_ms: start.elapsed().as_millis(),
            faults,
            patch: Some(patch),
            repaired_hub: patched_hub,
        };
    }

    RepairReport {
        already_healthy: false,
        repaired: false,
        candidates_evaluated,
        tests_passed_before,
        tests_total,
        tests_passed_after: tests_passed_before,
        safety_refuted_before,
        safety_refuted_after: safety_refuted_before,
        quickcheck_passed: false,
        elapsed_ms: start.elapsed().as_millis(),
        faults,
        patch: None,
        repaired_hub: numbered,
    }
}

/// Inject a realistic semantic bug into a healthy `HubModule` (flipping a relational boundary or
/// accumulator operator in a business logic function) so that unit tests fail and `repair_module`
/// can demonstrate end-to-end fault localization and CEGIS patch synthesis.
pub fn inject_demo_bug(hub: &HubModule) -> (HubModule, String) {
    let mut base = hub.clone();
    ensure_repair_stmt_ids(&mut base);

    let candidates = generate_repair_candidates(&base, &BTreeSet::new());
    for cand in candidates {
        if cand.func == "main" || cand.func.starts_with("test_") {
            continue;
        }
        let tests = eval_tests_default(&cand.patched_hub);
        let ver = verify_module(&cand.patched_hub);
        let any_test_failed = tests.iter().any(|t| !t.passed);
        if any_test_failed || ver.refuted > 0 {
            let desc = format!(
                "injected bug in {}() [stmt #{}]: {} -> {}",
                cand.func, cand.stmt_id, cand.before_summary, cand.after_summary
            );
            return (cand.patched_hub, desc);
        }
    }

    (base, "no injectable fault site found".to_string())
}

/// Check behavioral equivalence between all shared functions of `left_hub` and `right_hub`
/// using De Bruijn α-equivalence and QuickCheck bisimulation with minimal counterexample shrinking.
pub fn check_module_equivalence(
    left_hub: &HubModule,
    right_hub: &HubModule,
    trials_per_fn: usize,
) -> EquivalenceReport {
    let start = Instant::now();
    let seed_calls = collect_seed_call_args(left_hub);
    let mut functions = Vec::new();
    let mut all_equivalent = true;
    let mut alpha_identical_count = 0usize;
    let mut total_trials = 0usize;

    let left_fn_count = left_hub
        .items
        .iter()
        .filter(|i| matches!(i, Item::Function(_)))
        .count();
    let right_fn_count = right_hub
        .items
        .iter()
        .filter(|i| matches!(i, Item::Function(_)))
        .count();
    if left_fn_count != right_fn_count {
        all_equivalent = false;
    }

    for item in &left_hub.items {
        if let Item::Function(f_left) = item {
            let Some(f_right) = right_hub.find_fn(&f_left.name) else {
                all_equivalent = false;
                continue;
            };
            if f_left.params.len() != f_right.params.len()
                || f_left.ret_ty != f_right.ret_ty
                || f_left
                    .params
                    .iter()
                    .zip(&f_right.params)
                    .any(|(a, b)| a.ty != b.ty)
            {
                all_equivalent = false;
                continue;
            }

            let params_str: Vec<String> = f_left
                .params
                .iter()
                .map(|p| format!("{}: {}", p.name, p.ty.display()))
                .collect();
            let signature = format!(
                "fn {}({}) -> {}",
                f_left.name,
                params_str.join(", "),
                f_left.ret_ty.display()
            );

            let alpha_eq = normalize_fn_alpha(f_left) == normalize_fn_alpha(f_right);
            if alpha_eq {
                alpha_identical_count += 1;
            }

            let trials = if f_left.params.is_empty() {
                1
            } else {
                trials_per_fn.max(16)
            };
            let mut equivalent = true;
            let mut distinguishing: Option<MinimizedCounterexample> = None;
            let seed_args = seed_calls.get(&f_left.name);

            for t_idx in 0..trials {
                total_trials += 1;
                let args = gen_bisim_args(f_left, left_hub, seed_args, t_idx);
                let r_left = eval_fn_with_values(left_hub, &f_left.name, args.clone(), 20_000);
                let r_right = eval_fn_with_values(right_hub, &f_right.name, args.clone(), 20_000);

                let same = match (&r_left, &r_right) {
                    (Ok((v1, s1, _)), Ok((v2, s2, _))) => v1 == v2 && s1 == s2,
                    (Err(_), Err(_)) => true,
                    _ => false,
                };
                if !same {
                    equivalent = false;
                    all_equivalent = false;
                    if distinguishing.is_none() {
                        distinguishing = Some(shrink_bisim_counterexample(
                            left_hub,
                            right_hub,
                            &f_left.name,
                            &args,
                        ));
                    }
                    break;
                }
            }

            functions.push(FunctionEquivalence {
                name: f_left.name.clone(),
                signature,
                alpha_equivalent: alpha_eq,
                bisimulation_trials: trials,
                equivalent,
                distinguishing_counterexample: distinguishing,
            });
        }
    }

    EquivalenceReport {
        all_equivalent,
        shared_functions: functions.len(),
        alpha_identical_count,
        total_trials,
        elapsed_ms: start.elapsed().as_millis(),
        functions,
    }
}

fn shrink_bisim_counterexample(
    left_hub: &HubModule,
    right_hub: &HubModule,
    fn_name: &str,
    initial_args: &[Value],
) -> MinimizedCounterexample {
    // Use `shrink_failing_call` if right_hub crashes while left_hub succeeds
    if eval_fn_with_values(left_hub, fn_name, initial_args.to_vec(), 20_000).is_ok()
        && eval_fn_with_values(right_hub, fn_name, initial_args.to_vec(), 20_000).is_err()
    {
        if let Some(shrunk) = shrink_failing_call(right_hub, fn_name, initial_args) {
            return shrunk;
        }
    }
    let mut current = initial_args.to_vec();
    let mut shrink_steps = 0usize;
    for _ in 0..32 {
        let mut improved = false;
        for idx in 0..current.len() {
            for cand_val in shrink_value_candidates(&current[idx]) {
                let mut next = current.clone();
                next[idx] = cand_val;
                let r1 = eval_fn_with_values(left_hub, fn_name, next.clone(), 20_000);
                let r2 = eval_fn_with_values(right_hub, fn_name, next.clone(), 20_000);
                let same = match (&r1, &r2) {
                    (Ok((v1, s1, _)), Ok((v2, s2, _))) => v1 == v2 && s1 == s2,
                    (Err(_), Err(_)) => true,
                    _ => false,
                };
                if !same {
                    current = next;
                    shrink_steps += 1;
                    improved = true;
                    break;
                }
            }
        }
        if !improved {
            break;
        }
    }

    let r1 = eval_fn_with_values(left_hub, fn_name, current.clone(), 20_000)
        .map(|(v, _, _)| v.display_str())
        .unwrap_or_else(|e| format!("Err({})", e));
    let r2 = eval_fn_with_values(right_hub, fn_name, current.clone(), 20_000)
        .map(|(v, _, _)| v.display_str())
        .unwrap_or_else(|e| format!("Err({})", e));

    let fmt_tuple = |vals: &[Value]| -> String {
        let p: Vec<String> = vals.iter().map(|v| v.display_str()).collect();
        format!("({})", p.join(", "))
    };

    MinimizedCounterexample {
        fn_name: fn_name.to_string(),
        original_args: fmt_tuple(initial_args),
        minimized_args: fmt_tuple(&current),
        shrink_steps,
        fault: format!("left => {} != right => {}", r1, r2),
        repro_by_spoke: format_repro_across_spokes(left_hub, fn_name, &current),
    }
}

fn gen_bisim_args(
    f: &FnDecl,
    hub: &HubModule,
    seed_args: Option<&Vec<Value>>,
    trial_idx: usize,
) -> Vec<Value> {
    if trial_idx == 0 {
        if let Some(sa) = seed_args {
            if sa.len() == f.params.len() {
                return sa.clone();
            }
        }
    }
    f.params
        .iter()
        .enumerate()
        .map(|(i, p)| crate::complexity::default_value_for_type(&p.ty, hub, trial_idx + i))
        .collect()
}

fn normalize_fn_alpha(f: &FnDecl) -> String {
    let mut var_map: HashMap<String, String> = HashMap::new();
    let mut sig = Vec::new();
    for (idx, p) in f.params.iter().enumerate() {
        var_map.insert(p.name.clone(), format!("$v{}", idx));
        sig.push(format!("{:?}", p.ty));
    }
    let mut counter = f.params.len();
    let mut out = format!("fn({})->{:?}:", sig.join(","), f.ret_ty);
    normalize_stmts_alpha(&f.body, &mut var_map, &mut counter, &mut out);
    out
}

fn normalize_stmts_alpha(
    stmts: &[Stmt],
    var_map: &mut HashMap<String, String>,
    counter: &mut usize,
    out: &mut String,
) {
    for s in stmts {
        match s {
            Stmt::Comment { .. } => {}
            Stmt::Let { name, value, .. } => {
                let v_str = normalize_expr_alpha(value, var_map);
                let canon = format!("$v{}", *counter);
                *counter += 1;
                var_map.insert(name.clone(), canon.clone());
                out.push_str(&format!("(let {} {});", canon, v_str));
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let tgt_str = match target {
                    AssignTarget::Var(v) => var_map
                        .get(v)
                        .cloned()
                        .unwrap_or_else(|| v.to_string()),
                    AssignTarget::Field { base, field } => {
                        let b = var_map
                            .get(base)
                            .cloned()
                            .unwrap_or_else(|| base.to_string());
                        format!("{}.{}", b, field)
                    }
                    AssignTarget::Index { base, index } => {
                        let b = var_map
                            .get(base)
                            .cloned()
                            .unwrap_or_else(|| base.to_string());
                        format!("{}[{}]", b, normalize_expr_alpha(index, var_map))
                    }
                };
                let val_str = normalize_expr_alpha(value, var_map);
                let canon_rhs = match op {
                    AssignOp::Set => val_str,
                    AssignOp::AddAssign => format!("(Add {} {})", tgt_str, val_str),
                    AssignOp::SubAssign => format!("(Sub {} {})", tgt_str, val_str),
                };
                out.push_str(&format!("(assign {} Set {});", tgt_str, canon_rhs));
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                out.push_str(&format!("(if {} [", normalize_expr_alpha(cond, var_map)));
                let mut then_map = var_map.clone();
                normalize_stmts_alpha(then_body, &mut then_map, counter, out);
                out.push_str("] [");
                let mut else_map = var_map.clone();
                normalize_stmts_alpha(else_body, &mut else_map, counter, out);
                out.push_str("]);");
            }
            Stmt::Match { expr, arms, .. } => {
                out.push_str(&format!("(match {} [", normalize_expr_alpha(expr, var_map)));
                for arm in arms {
                    let pat_str = match &arm.pat {
                        MatchPat::EnumVariant { enum_name, variant } => {
                            format!("{}::{}", enum_name, variant)
                        }
                        MatchPat::Int(v) => v.to_string(),
                        MatchPat::Str(s) => format!("{:?}", s),
                        MatchPat::Wildcard => "_".to_string(),
                    };
                    out.push_str(&format!("({} => [", pat_str));
                    let mut arm_map = var_map.clone();
                    normalize_stmts_alpha(&arm.body, &mut arm_map, counter, out);
                    out.push_str("])");
                }
                out.push_str("]);");
            }
            Stmt::While { cond, body, .. } => {
                out.push_str(&format!("(while {} [", normalize_expr_alpha(cond, var_map)));
                let mut body_map = var_map.clone();
                normalize_stmts_alpha(body, &mut body_map, counter, out);
                out.push_str("]);");
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                let s_str = normalize_expr_alpha(start, var_map);
                let e_str = normalize_expr_alpha(end, var_map);
                let mut body_map = var_map.clone();
                let canon = format!("$v{}", *counter);
                *counter += 1;
                body_map.insert(var.clone(), canon.clone());
                out.push_str(&format!("(for-range {} {} {} [", canon, s_str, e_str));
                normalize_stmts_alpha(body, &mut body_map, counter, out);
                out.push_str("]);");
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let it_str = normalize_expr_alpha(iter, var_map);
                let mut body_map = var_map.clone();
                let canon = format!("$v{}", *counter);
                *counter += 1;
                body_map.insert(var.clone(), canon.clone());
                out.push_str(&format!("(for-each {} {} [", canon, it_str));
                normalize_stmts_alpha(body, &mut body_map, counter, out);
                out.push_str("]);");
            }
            Stmt::Break { .. } => out.push_str("(break);"),
            Stmt::Continue { .. } => out.push_str("(continue);"),
            Stmt::Return { value, .. } => {
                let v = value
                    .as_ref()
                    .map(|e| normalize_expr_alpha(e, var_map))
                    .unwrap_or_default();
                out.push_str(&format!("(ret {});", v));
            }
            Stmt::Assert { cond, .. } => {
                out.push_str(&format!("(assert {});", normalize_expr_alpha(cond, var_map)));
            }
            Stmt::AssertEq { left, right, .. } => {
                out.push_str(&format!(
                    "(assert-eq {} {});",
                    normalize_expr_alpha(left, var_map),
                    normalize_expr_alpha(right, var_map)
                ));
            }
            Stmt::Expr { expr, .. } => {
                out.push_str(&format!("(expr {});", normalize_expr_alpha(expr, var_map)));
            }
        }
    }
}

fn normalize_expr_alpha(e: &Expr, var_map: &HashMap<String, String>) -> String {
    match e {
        Expr::Int(v) => {
            if *v < 0 && *v > i64::MIN {
                format!("({:?} {})", UnaryOp::Neg, -*v)
            } else {
                v.to_string()
            }
        }
        Expr::Float(v) => {
            if *v < 0.0 {
                format!("({:?} {})", UnaryOp::Neg, -*v)
            } else {
                format!("{}", v)
            }
        }
        Expr::Bool(b) => b.to_string(),
        Expr::Str(s) => format!("{:?}", s),
        Expr::Var(name) => var_map
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.clone()),
        Expr::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
        Expr::Binary { op, left, right } => format!(
            "({:?} {} {})",
            op,
            normalize_expr_alpha(left, var_map),
            normalize_expr_alpha(right, var_map)
        ),
        Expr::Unary { op, expr: inner } => {
            format!("({:?} {})", op, normalize_expr_alpha(inner, var_map))
        }
        Expr::Call { func, args } => {
            let a: Vec<String> = args
                .iter()
                .map(|x| normalize_expr_alpha(x, var_map))
                .collect();
            format!("(call {} [{}])", func, a.join(","))
        }
        Expr::Index { base, index } => format!(
            "(idx {} {})",
            normalize_expr_alpha(base, var_map),
            normalize_expr_alpha(index, var_map)
        ),
        Expr::FieldAccess { base, field } => {
            format!("(fld {} {})", normalize_expr_alpha(base, var_map), field)
        }
        Expr::List(items) => {
            let p: Vec<String> = items
                .iter()
                .map(|x| normalize_expr_alpha(x, var_map))
                .collect();
            format!("(list [{}])", p.join(","))
        }
        Expr::StructInit { name, fields } => {
            let mut p: Vec<String> = fields
                .iter()
                .map(|(fname, fval)| format!("{}:{}", fname, normalize_expr_alpha(fval, var_map)))
                .collect();
            p.sort();
            format!("(struct {} {{{}}})", name, p.join(","))
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(a) => format!("(len {})", normalize_expr_alpha(a, var_map)),
            Intrinsic::Min(a, b) => format!(
                "(min {} {})",
                normalize_expr_alpha(a, var_map),
                normalize_expr_alpha(b, var_map)
            ),
            Intrinsic::Max(a, b) => format!(
                "(max {} {})",
                normalize_expr_alpha(a, var_map),
                normalize_expr_alpha(b, var_map)
            ),
            Intrinsic::Abs(a) => format!("(abs {})", normalize_expr_alpha(a, var_map)),
            Intrinsic::Push { list, value } => format!(
                "(push {} {})",
                normalize_expr_alpha(list, var_map),
                normalize_expr_alpha(value, var_map)
            ),
            Intrinsic::Contains { haystack, needle } => format!(
                "(contains {} {})",
                normalize_expr_alpha(haystack, var_map),
                normalize_expr_alpha(needle, var_map)
            ),
            Intrinsic::Upper(a) => format!("(upper {})", normalize_expr_alpha(a, var_map)),
            Intrinsic::Lower(a) => format!("(lower {})", normalize_expr_alpha(a, var_map)),
            Intrinsic::ToStr(a) => format!("(to-str {})", normalize_expr_alpha(a, var_map)),
            Intrinsic::Print(args) => {
                let p: Vec<String> = args
                    .iter()
                    .map(|x| normalize_expr_alpha(x, var_map))
                    .collect();
                format!("(print [{}])", p.join(","))
            }
        },
    }
}

struct CandidatePatch {
    stmt_id: NodeId,
    func: String,
    kind: String,
    before_summary: String,
    after_summary: String,
    patched_hub: HubModule,
}

fn localize_faults(
    numbered: &HubModule,
    tests: &[crate::eval::TestResult],
    ver: &crate::verify::VerifyReport,
    stmt_spoke_lines: &BTreeMap<NodeId, BTreeMap<String, usize>>,
) -> (Vec<FaultLocation>, BTreeSet<NodeId>) {
    let mut faults = Vec::new();
    let mut priority_ids = BTreeSet::new();

    for ob in &ver.obligations {
        if let crate::verify::VerifyStatus::Refuted {
            witness_call,
            runtime_error,
        } = &ob.status
        {
            let mut matched_sids = Vec::new();
            if let Some(f) = numbered.find_fn(&ob.func) {
                collect_fn_stmt_ids(&f.body, &mut matched_sids);
            }
            let ob_nid = matched_sids.first().copied().unwrap_or(ob.id as NodeId);
            for sid in matched_sids {
                priority_ids.insert(sid);
            }
            priority_ids.insert(ob_nid);
            faults.push(FaultLocation {
                stmt_id: ob_nid,
                func: ob.func.clone(),
                symptom: format!(
                    "Refuted safety obligation `{}` via {} => {}",
                    ob.expr_summary, witness_call, runtime_error
                ),
                spoke_lines: stmt_spoke_lines.get(&ob_nid).cloned().unwrap_or_default(),
            });
        }
    }

    for tr in tests.iter().filter(|t| !t.passed) {
        let tt = record_time_travel_default(numbered, Some("fault"));
        if let Some(sl) = &tt.slice {
            for &step_idx in &sl.slice_steps {
                if let Some(st) = tt.steps.get(step_idx) {
                    priority_ids.insert(st.stmt_id);
                }
            }
        }
        for st in tt.steps.iter().rev().take(6) {
            if st.func != "main" && !st.func.starts_with("test_") {
                priority_ids.insert(st.stmt_id);
                if faults.len() < 3 {
                    faults.push(FaultLocation {
                        stmt_id: st.stmt_id,
                        func: st.func.clone(),
                        symptom: format!(
                            "Unit test `test_{}` failed ({}) — backward slice includes `{}`",
                            tr.name,
                            tr.error.as_deref().unwrap_or("assertion failed"),
                            st.summary
                        ),
                        spoke_lines: st.spoke_lines.clone(),
                    });
                }
                break;
            }
        }
    }

    (faults, priority_ids)
}

fn generate_repair_candidates(
    numbered: &HubModule,
    priority_ids: &BTreeSet<NodeId>,
) -> Vec<CandidatePatch> {
    let mut prioritized = Vec::new();
    let mut fallback = Vec::new();

    for (item_idx, item) in numbered.items.iter().enumerate() {
        let Item::Function(f) = item else {
            continue;
        };
        if f.name == "main" {
            continue;
        }
        let mut path = Vec::new();
        collect_stmt_candidates(
            numbered,
            item_idx,
            &f.name,
            &f.body,
            &mut path,
            priority_ids,
            &mut prioritized,
            &mut fallback,
        );
    }

    prioritized.extend(fallback);
    prioritized
}

#[allow(clippy::too_many_arguments)]
fn collect_stmt_candidates(
    base_hub: &HubModule,
    item_idx: usize,
    fn_name: &str,
    stmts: &[Stmt],
    path: &mut Vec<usize>,
    priority_ids: &BTreeSet<NodeId>,
    prioritized: &mut Vec<CandidatePatch>,
    fallback: &mut Vec<CandidatePatch>,
) {
    for (idx, stmt) in stmts.iter().enumerate() {
        path.push(idx);
        let sid = stmt_id_of(stmt);
        let is_prio = priority_ids.is_empty() || priority_ids.contains(&sid);
        let out_vec = if is_prio {
            &mut *prioritized
        } else {
            &mut *fallback
        };

        // Generate single-statement mutations at `path`
        for (kind, before_s, after_s, new_stmt) in mutate_single_stmt_for_repair(stmt) {
            let mut cloned = base_hub.clone();
            if let Some(Item::Function(f_mut)) = cloned.items.get_mut(item_idx) {
                if replace_stmt_at_path(&mut f_mut.body, path, new_stmt) {
                    out_vec.push(CandidatePatch {
                        stmt_id: sid,
                        func: fn_name.to_string(),
                        kind,
                        before_summary: before_s,
                        after_summary: after_s,
                        patched_hub: cloned,
                    });
                }
            }
        }

        // Recurse into nested blocks
        match stmt {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                path.push(0);
                collect_stmt_candidates(
                    base_hub,
                    item_idx,
                    fn_name,
                    then_body,
                    path,
                    priority_ids,
                    prioritized,
                    fallback,
                );
                *path.last_mut().unwrap() = 1;
                collect_stmt_candidates(
                    base_hub,
                    item_idx,
                    fn_name,
                    else_body,
                    path,
                    priority_ids,
                    prioritized,
                    fallback,
                );
                path.pop();
            }
            Stmt::Match { arms, .. } => {
                for (a_idx, arm) in arms.iter().enumerate() {
                    path.push(a_idx);
                    collect_stmt_candidates(
                        base_hub,
                        item_idx,
                        fn_name,
                        &arm.body,
                        path,
                        priority_ids,
                        prioritized,
                        fallback,
                    );
                    path.pop();
                }
            }
            Stmt::While { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::ForRange { body, .. } => {
                path.push(0);
                collect_stmt_candidates(
                    base_hub,
                    item_idx,
                    fn_name,
                    body,
                    path,
                    priority_ids,
                    prioritized,
                    fallback,
                );
                path.pop();
            }
            _ => {}
        }

        path.pop();
    }
}

fn replace_stmt_at_path(stmts: &mut [Stmt], path: &[usize], replacement: Stmt) -> bool {
    if path.is_empty() {
        return false;
    }
    let idx = path[0];
    let Some(cur) = stmts.get_mut(idx) else {
        return false;
    };
    if path.len() == 1 {
        *cur = replacement;
        return true;
    }
    let branch_idx = path[1];
    let rest = &path[2..];
    match cur {
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            if branch_idx == 0 {
                replace_stmt_at_path(then_body, rest, replacement)
            } else {
                replace_stmt_at_path(else_body, rest, replacement)
            }
        }
        Stmt::Match { arms, .. } => {
            if let Some(arm) = arms.get_mut(branch_idx) {
                replace_stmt_at_path(&mut arm.body, rest, replacement)
            } else {
                false
            }
        }
        Stmt::While { body, .. }
        | Stmt::ForEach { body, .. }
        | Stmt::ForRange { body, .. } => replace_stmt_at_path(body, rest, replacement),
        _ => false,
    }
}

fn collect_fn_stmt_ids(stmts: &[Stmt], out: &mut Vec<NodeId>) {
    for s in stmts {
        let sid = stmt_id_of(s);
        if sid > 0 {
            out.push(sid);
        }
        match s {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_fn_stmt_ids(then_body, out);
                collect_fn_stmt_ids(else_body, out);
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    collect_fn_stmt_ids(&a.body, out);
                }
            }
            Stmt::While { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::ForRange { body, .. } => {
                collect_fn_stmt_ids(body, out);
            }
            _ => {}
        }
    }
}

fn mutate_single_stmt_for_repair(stmt: &Stmt) -> Vec<(String, String, String, Stmt)> {
    let mut out = Vec::new();
    match stmt {
        Stmt::If {
            id,
            cond,
            then_body,
            else_body,
            meta,
        } => {
            for (kind, b_str, a_str, new_cond) in mutate_expr_for_repair(cond) {
                out.push((
                    kind,
                    format!("if ({})", b_str),
                    format!("if ({})", a_str),
                    Stmt::If {
                        id: *id,
                        cond: new_cond,
                        then_body: then_body.clone(),
                        else_body: else_body.clone(),
                        meta: meta.clone(),
                    },
                ));
            }
        }
        Stmt::While {
            id,
            cond,
            body,
            meta,
        } => {
            for (kind, b_str, a_str, new_cond) in mutate_expr_for_repair(cond) {
                out.push((
                    kind,
                    format!("while ({})", b_str),
                    format!("while ({})", a_str),
                    Stmt::While {
                        id: *id,
                        cond: new_cond,
                        body: body.clone(),
                        meta: meta.clone(),
                    },
                ));
            }
        }
        Stmt::Assign {
            id,
            target,
            op,
            value,
            meta,
        } => {
            // 1. Compound assignment flip (+= <-> -=)
            if *op == AssignOp::AddAssign {
                out.push((
                    "AccumulatorOpRepair".to_string(),
                    format!("{} += ...", target.root_var()),
                    format!("{} -= ...", target.root_var()),
                    Stmt::Assign {
                        id: *id,
                        target: target.clone(),
                        op: AssignOp::SubAssign,
                        value: value.clone(),
                        meta: meta.clone(),
                    },
                ));
            } else if *op == AssignOp::SubAssign {
                out.push((
                    "AccumulatorOpRepair".to_string(),
                    format!("{} -= ...", target.root_var()),
                    format!("{} += ...", target.root_var()),
                    Stmt::Assign {
                        id: *id,
                        target: target.clone(),
                        op: AssignOp::AddAssign,
                        value: value.clone(),
                        meta: meta.clone(),
                    },
                ));
            }
            // 2. Expression-level repair on RHS (and index target if present)
            if let AssignTarget::Index { base, index } = target {
                for (kind, b_str, a_str, new_idx) in mutate_expr_for_repair(index) {
                    out.push((
                        kind,
                        format!("{}[{}] = ...", base, b_str),
                        format!("{}[{}] = ...", base, a_str),
                        Stmt::Assign {
                            id: *id,
                            target: AssignTarget::Index {
                                base: base.clone(),
                                index: new_idx,
                            },
                            op: *op,
                            value: value.clone(),
                            meta: meta.clone(),
                        },
                    ));
                }
            }
            for (kind, b_str, a_str, new_val) in mutate_expr_for_repair(value) {
                out.push((
                    kind,
                    format!("{} = {}", target.root_var(), b_str),
                    format!("{} = {}", target.root_var(), a_str),
                    Stmt::Assign {
                        id: *id,
                        target: target.clone(),
                        op: *op,
                        value: new_val,
                        meta: meta.clone(),
                    },
                ));
            }
        }
        Stmt::Let {
            id,
            name,
            mutable,
            ty,
            value,
            meta,
        } => {
            for (kind, b_str, a_str, new_val) in mutate_expr_for_repair(value) {
                out.push((
                    kind,
                    format!("let {} = {}", name, b_str),
                    format!("let {} = {}", name, a_str),
                    Stmt::Let {
                        id: *id,
                        name: name.clone(),
                        mutable: *mutable,
                        ty: ty.clone(),
                        value: new_val,
                        meta: meta.clone(),
                    },
                ));
            }
        }
        Stmt::Return {
            id,
            value: Some(val),
            meta,
        } => {
            for (kind, b_str, a_str, new_val) in mutate_expr_for_repair(val) {
                out.push((
                    kind,
                    format!("return {}", b_str),
                    format!("return {}", a_str),
                    Stmt::Return {
                        id: *id,
                        value: Some(new_val),
                        meta: meta.clone(),
                    },
                ));
            }
        }
        Stmt::ForRange {
            id,
            var,
            start,
            end,
            body,
            meta,
        } => {
            if let Expr::Binary {
                op: BinOp::Sub | BinOp::Add,
                left,
                right,
            } = end
            {
                if matches!(right.as_ref(), Expr::Int(1)) {
                    out.push((
                        "LoopBoundaryOffByOneRepair".to_string(),
                        format!("for {} in ..({:?} 1)", var, end),
                        format!("for {} in ..{:?}", var, left),
                        Stmt::ForRange {
                            id: *id,
                            var: var.clone(),
                            start: start.clone(),
                            end: (**left).clone(),
                            body: body.clone(),
                            meta: meta.clone(),
                        },
                    ));
                }
            }
            for (kind, b_str, a_str, new_end) in mutate_expr_for_repair(end) {
                out.push((
                    kind,
                    format!("for {} in ..({})", var, b_str),
                    format!("for {} in ..({})", var, a_str),
                    Stmt::ForRange {
                        id: *id,
                        var: var.clone(),
                        start: start.clone(),
                        end: new_end,
                        body: body.clone(),
                        meta: meta.clone(),
                    },
                ));
            }
        }
        _ => {}
    }
    out
}

fn mutate_expr_for_repair(expr: &Expr) -> Vec<(String, String, String, Expr)> {
    let mut out = Vec::new();
    match expr {
        Expr::Binary { op, left, right } => {
            let replacements: &[(&str, BinOp)] = match op {
                BinOp::Gt => &[("RelationalBoundaryRepair", BinOp::Ge)],
                BinOp::Ge => &[("RelationalBoundaryRepair", BinOp::Gt)],
                BinOp::Lt => &[("RelationalBoundaryRepair", BinOp::Le)],
                BinOp::Le => &[("RelationalBoundaryRepair", BinOp::Lt)],
                BinOp::Eq => &[("RelationalEqualityRepair", BinOp::Ne)],
                BinOp::Ne => &[("RelationalEqualityRepair", BinOp::Eq)],
                BinOp::Add => &[("ArithmeticSignRepair", BinOp::Sub)],
                BinOp::Sub => &[("ArithmeticSignRepair", BinOp::Add)],
                BinOp::Mul => &[("ArithmeticFactorRepair", BinOp::IntDiv)],
                BinOp::IntDiv | BinOp::Div => &[("ArithmeticFactorRepair", BinOp::Mul)],
                BinOp::And => &[("LogicalOperatorRepair", BinOp::Or)],
                BinOp::Or => &[("LogicalOperatorRepair", BinOp::And)],
                _ => &[],
            };
            for &(kind, new_op) in replacements {
                out.push((
                    kind.to_string(),
                    format!("{:?}", op),
                    format!("{:?}", new_op),
                    Expr::Binary {
                        op: new_op,
                        left: left.clone(),
                        right: right.clone(),
                    },
                ));
            }
            // Also offer safety-clamping `max(0, a // b)` on unguarded integer division
            if *op == BinOp::IntDiv {
                let guarded_div = Expr::Binary {
                    op: BinOp::IntDiv,
                    left: left.clone(),
                    right: Box::new(Expr::Intrinsic(Box::new(Intrinsic::Max(
                        Expr::Int(1),
                        (**right).clone(),
                    )))),
                };
                out.push((
                    "SafetyDivisorGuard".to_string(),
                    "x // y".to_string(),
                    "max(0, x // max(1, y))".to_string(),
                    Expr::Intrinsic(Box::new(Intrinsic::Max(Expr::Int(0), guarded_div))),
                ));
            }
            // Recurse into left & right operands
            for (kind, b_s, a_s, nl) in mutate_expr_for_repair(left) {
                out.push((
                    kind,
                    b_s,
                    a_s,
                    Expr::Binary {
                        op: *op,
                        left: Box::new(nl),
                        right: right.clone(),
                    },
                ));
            }
            for (kind, b_s, a_s, nr) in mutate_expr_for_repair(right) {
                out.push((
                    kind,
                    b_s,
                    a_s,
                    Expr::Binary {
                        op: *op,
                        left: left.clone(),
                        right: Box::new(nr),
                    },
                ));
            }
        }
        Expr::Unary { op, expr: inner } => {
            for (kind, b_s, a_s, ni) in mutate_expr_for_repair(inner) {
                out.push((
                    kind,
                    b_s,
                    a_s,
                    Expr::Unary {
                        op: *op,
                        expr: Box::new(ni),
                    },
                ));
            }
        }
        Expr::Call { func, args } => {
            for (idx, arg) in args.iter().enumerate() {
                for (kind, b_s, a_s, na) in mutate_expr_for_repair(arg) {
                    let mut new_args = args.clone();
                    new_args[idx] = na;
                    out.push((
                        kind,
                        b_s,
                        a_s,
                        Expr::Call {
                            func: func.clone(),
                            args: new_args,
                        },
                    ));
                }
            }
        }
        Expr::Index { base, index } => {
            for (kind, b_s, a_s, ni) in mutate_expr_for_repair(index) {
                out.push((
                    kind,
                    b_s,
                    a_s,
                    Expr::Index {
                        base: base.clone(),
                        index: Box::new(ni),
                    },
                ));
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Min(a, b) => {
                out.push((
                    "ExtremumSwapRepair".to_string(),
                    "min(a, b)".to_string(),
                    "max(a, b)".to_string(),
                    Expr::Intrinsic(Box::new(Intrinsic::Max(a.clone(), b.clone()))),
                ));
                for (kind, b_s, a_s, na) in mutate_expr_for_repair(a) {
                    out.push((
                        kind,
                        b_s,
                        a_s,
                        Expr::Intrinsic(Box::new(Intrinsic::Min(na, b.clone()))),
                    ));
                }
                for (kind, b_s, a_s, nb) in mutate_expr_for_repair(b) {
                    out.push((
                        kind,
                        b_s,
                        a_s,
                        Expr::Intrinsic(Box::new(Intrinsic::Min(a.clone(), nb))),
                    ));
                }
            }
            Intrinsic::Max(a, b) => {
                out.push((
                    "ExtremumSwapRepair".to_string(),
                    "max(a, b)".to_string(),
                    "min(a, b)".to_string(),
                    Expr::Intrinsic(Box::new(Intrinsic::Min(a.clone(), b.clone()))),
                ));
                for (kind, b_s, a_s, na) in mutate_expr_for_repair(a) {
                    out.push((
                        kind,
                        b_s,
                        a_s,
                        Expr::Intrinsic(Box::new(Intrinsic::Max(na, b.clone()))),
                    ));
                }
                for (kind, b_s, a_s, nb) in mutate_expr_for_repair(b) {
                    out.push((
                        kind,
                        b_s,
                        a_s,
                        Expr::Intrinsic(Box::new(Intrinsic::Max(a.clone(), nb))),
                    ));
                }
            }
            Intrinsic::Abs(a) => {
                for (kind, b_s, a_s, na) in mutate_expr_for_repair(a) {
                    out.push((
                        kind,
                        b_s,
                        a_s,
                        Expr::Intrinsic(Box::new(Intrinsic::Abs(na))),
                    ));
                }
            }
            _ => {}
        },
        _ => {}
    }
    out
}

fn compute_spoke_patch_diffs(
    before_hub: &HubModule,
    after_hub: &HubModule,
) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for spoke in SpokeId::ALL {
        let lens = lens_for(spoke);
        let before_src = lens.get(before_hub);
        let after_src = lens.get(after_hub);
        let b_lines: Vec<&str> = before_src.lines().collect();
        let a_lines: Vec<&str> = after_src.lines().collect();
        let max_len = b_lines.len().max(a_lines.len());
        let mut hunks = Vec::new();
        for idx in 0..max_len {
            let bl = b_lines.get(idx).copied().unwrap_or("");
            let al = a_lines.get(idx).copied().unwrap_or("");
            if bl != al {
                hunks.push(format!("L{}: - {}\nL{}: + {}", idx + 1, bl.trim(), idx + 1, al.trim()));
            }
        }
        out.insert(spoke.as_str().to_string(), hunks.join("\n"));
    }
    out
}

fn stmt_id_of(s: &Stmt) -> NodeId {
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

fn ensure_repair_stmt_ids(hub: &mut HubModule) {
    fn number(stmts: &mut [Stmt], next_id: &mut NodeId) {
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
                    number(then_body, next_id);
                    number(else_body, next_id);
                }
                Stmt::Match { id, arms, .. } => {
                    if *id == 0 {
                        *id = *next_id;
                        *next_id += 1;
                    }
                    for a in arms {
                        number(&mut a.body, next_id);
                    }
                }
                Stmt::While { id, body, .. }
                | Stmt::ForEach { id, body, .. }
                | Stmt::ForRange { id, body, .. } => {
                    if *id == 0 {
                        *id = *next_id;
                        *next_id += 1;
                    }
                    number(body, next_id);
                }
            }
        }
    }

    let mut next_id = hub.next_id.max(1000);
    for item in &mut hub.items {
        match item {
            Item::Function(f) => number(&mut f.body, &mut next_id),
            Item::Test(t) => number(&mut t.body, &mut next_id),
            _ => {}
        }
    }
}

use std::collections::BTreeMap;
use std::time::Instant;

use crate::complexity::{collect_seed_call_args, default_value_for_type};
use crate::eval::{eval_fn_with_values, Value};
use crate::hub::{
    Expr, FnDecl, HubModule, Item, Metadata, Stmt, TestDecl, Type,
};
use crate::lens::SpokeId;
use crate::refactor::optimize_module;
use crate::spokes::lens_for;

const DEFAULT_QC_TRIALS: usize = 64;
const MAX_QC_STEPS: usize = 25_000;

#[derive(Debug, Clone)]
pub struct MinimizedCounterexample {
    pub fn_name: String,
    pub original_args: String,
    pub minimized_args: String,
    pub shrink_steps: usize,
    pub fault: String,
    pub repro_by_spoke: BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct FunctionQuickCheck {
    pub name: String,
    pub signature: String,
    pub trials_run: usize,
    pub passed_trials: usize,
    pub contract_safe: bool,
    pub optimizer_equivalent: bool,
    pub deterministic: bool,
    pub discovered_invariants: Vec<String>,
    pub counterexample: Option<MinimizedCounterexample>,
}

#[derive(Debug, Clone)]
pub struct QuickCheckReport {
    pub seed: u64,
    pub trials_per_fn: usize,
    pub total_functions: usize,
    pub total_trials: usize,
    pub all_passed: bool,
    pub optimizer_checks: usize,
    pub total_invariants: usize,
    pub elapsed_ms: u128,
    pub functions: Vec<FunctionQuickCheck>,
}

pub fn run_quickcheck_default(hub: &HubModule) -> QuickCheckReport {
    run_quickcheck(hub, DEFAULT_QC_TRIALS, 0x57A4_2026_1100)
}

pub fn run_quickcheck(
    hub: &HubModule,
    trials_per_fn: usize,
    seed: u64,
) -> QuickCheckReport {
    let start = Instant::now();
    let (opt_hub, _) = optimize_module(hub);
    let seed_calls = collect_seed_call_args(hub);
    let mut rng = QcRng::new(seed);

    let mut functions = Vec::new();
    let mut total_trials = 0usize;
    let mut optimizer_checks = 0usize;
    let mut total_invariants = 0usize;
    let mut all_passed = true;

    for item in &hub.items {
        if let Item::Function(f) = item {
            let fqc = check_single_function(
                f,
                hub,
                &opt_hub,
                seed_calls.get(&f.name),
                trials_per_fn,
                &mut rng,
            );
            total_trials += fqc.trials_run;
            optimizer_checks += fqc.passed_trials;
            total_invariants += fqc.discovered_invariants.len();
            if !fqc.contract_safe || !fqc.optimizer_equivalent || !fqc.deterministic {
                all_passed = false;
            }
            functions.push(fqc);
        }
    }

    QuickCheckReport {
        seed,
        trials_per_fn,
        total_functions: functions.len(),
        total_trials,
        all_passed,
        optimizer_checks,
        total_invariants,
        elapsed_ms: start.elapsed().as_millis(),
        functions,
    }
}

fn check_single_function(
    f: &FnDecl,
    hub: &HubModule,
    opt_hub: &HubModule,
    seed_args: Option<&Vec<Value>>,
    trials_per_fn: usize,
    rng: &mut QcRng,
) -> FunctionQuickCheck {
    let params_str: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.ty.display()))
        .collect();
    let signature = format!("fn {}({}) -> {}", f.name, params_str.join(", "), f.ret_ty.display());

    let effective_trials = if f.params.is_empty() {
        1
    } else {
        trials_per_fn.max(8)
    };

    let mut trials_run = 0usize;
    let mut passed_trials = 0usize;
    let mut contract_safe = true;
    let mut optimizer_equivalent = true;
    let mut deterministic = true;
    let mut counterexample: Option<MinimizedCounterexample> = None;
    let mut observations: Vec<(Vec<Value>, Value)> = Vec::new();

    for trial_idx in 0..effective_trials {
        let args = synthesize_trial_args(f, hub, seed_args, trial_idx, rng);
        trials_run += 1;

        match eval_fn_with_values(hub, &f.name, args.clone(), MAX_QC_STEPS) {
            Ok((ret_val, stdout_unopt, steps_unopt)) => {
                passed_trials += 1;

                // 1. Check equivalence against constant-folded & dead-branch-pruned Hub AST
                match eval_fn_with_values(opt_hub, &f.name, args.clone(), MAX_QC_STEPS) {
                    Ok((ret_opt, stdout_opt, _)) => {
                        if ret_val != ret_opt || stdout_unopt != stdout_opt {
                            optimizer_equivalent = false;
                            if counterexample.is_none() {
                                counterexample = Some(shrink_counterexample(
                                    hub,
                                    &f.name,
                                    &args,
                                    "optimizer equivalence mismatch",
                                    |cand| {
                                        let r1 = eval_fn_with_values(
                                            hub,
                                            &f.name,
                                            cand.to_vec(),
                                            MAX_QC_STEPS,
                                        );
                                        let r2 = eval_fn_with_values(
                                            opt_hub,
                                            &f.name,
                                            cand.to_vec(),
                                            MAX_QC_STEPS,
                                        );
                                        match (r1, r2) {
                                            (Ok((v1, s1, _)), Ok((v2, s2, _))) => {
                                                if v1 != v2 || s1 != s2 {
                                                    Some(format!(
                                                        "unopt {:?} != opt {:?}",
                                                        v1.display_str(),
                                                        v2.display_str()
                                                    ))
                                                } else {
                                                    None
                                                }
                                            }
                                            _ => None,
                                        }
                                    },
                                ));
                            }
                        }
                    }
                    Err(e) => {
                        optimizer_equivalent = false;
                        if counterexample.is_none() {
                            counterexample = Some(shrink_counterexample(
                                hub,
                                &f.name,
                                &args,
                                &e,
                                |cand| {
                                    eval_fn_with_values(opt_hub, &f.name, cand.to_vec(), MAX_QC_STEPS)
                                        .err()
                                },
                            ));
                        }
                    }
                }

                // 2. Spot-check determinism on first 4 trials
                if trial_idx < 4 {
                    if let Ok((ret2, out2, steps2)) =
                        eval_fn_with_values(hub, &f.name, args.clone(), MAX_QC_STEPS)
                    {
                        if ret2 != ret_val || out2 != stdout_unopt || steps2 != steps_unopt {
                            deterministic = false;
                        }
                    }
                }

                observations.push((args, ret_val));
            }
            Err(fault) => {
                contract_safe = false;
                if counterexample.is_none() {
                    counterexample = Some(shrink_failing_call_with_fault(
                        hub,
                        &f.name,
                        &args,
                        &fault,
                    ));
                }
            }
        }
    }

    let discovered_invariants = infer_invariants(f, hub, &observations);

    FunctionQuickCheck {
        name: f.name.clone(),
        signature,
        trials_run,
        passed_trials,
        contract_safe,
        optimizer_equivalent,
        deterministic,
        discovered_invariants,
        counterexample,
    }
}

/// Shrink an initial failing argument vector `initial_args` on `fn_name` down to a minimal
/// counterexample using multi-pass Delta-Debugging across lists, integers, floats, strings, and structs.
pub fn shrink_failing_call(
    hub: &HubModule,
    fn_name: &str,
    initial_args: &[Value],
) -> Option<MinimizedCounterexample> {
    let initial_fault = eval_fn_with_values(hub, fn_name, initial_args.to_vec(), MAX_QC_STEPS).err()?;
    Some(shrink_failing_call_with_fault(
        hub,
        fn_name,
        initial_args,
        &initial_fault,
    ))
}

fn shrink_failing_call_with_fault(
    hub: &HubModule,
    fn_name: &str,
    initial_args: &[Value],
    initial_fault: &str,
) -> MinimizedCounterexample {
    shrink_counterexample(hub, fn_name, initial_args, initial_fault, |cand| {
        eval_fn_with_values(hub, fn_name, cand.to_vec(), MAX_QC_STEPS).err()
    })
}

fn shrink_counterexample<F>(
    hub: &HubModule,
    fn_name: &str,
    initial_args: &[Value],
    initial_fault: &str,
    mut fails_pred: F,
) -> MinimizedCounterexample
where
    F: FnMut(&[Value]) -> Option<String>,
{
    let original_args = format_value_tuple(initial_args);
    let mut current = initial_args.to_vec();
    let mut current_fault = initial_fault.to_string();
    let mut shrink_steps = 0usize;

    // Multi-pass coordinate-wise shrinking until fixed point (up to 64 rounds)
    for _round in 0..64 {
        let mut improved = false;
        for arg_idx in 0..current.len() {
            let candidates = shrink_value_candidates(&current[arg_idx]);
            for cand_val in candidates {
                let mut next_args = current.clone();
                next_args[arg_idx] = cand_val;
                if let Some(new_fault) = fails_pred(&next_args) {
                    current = next_args;
                    current_fault = new_fault;
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

    let minimized_args = format_value_tuple(&current);
    let repro_by_spoke = format_repro_across_spokes(hub, fn_name, &current);

    MinimizedCounterexample {
        fn_name: fn_name.to_string(),
        original_args,
        minimized_args,
        shrink_steps,
        fault: current_fault,
        repro_by_spoke,
    }
}

pub(crate) fn shrink_value_candidates(val: &Value) -> Vec<Value> {
    let mut out = Vec::new();
    match val {
        Value::Int(v) => {
            if *v != 0 {
                out.push(Value::Int(0));
                if *v < 0 {
                    if let Some(neg) = v.checked_neg() {
                        out.push(Value::Int(neg));
                    }
                    if *v < -1 {
                        out.push(Value::Int(-1));
                    }
                } else if *v > 1 {
                    out.push(Value::Int(1));
                }
                let half = *v / 2;
                if half != 0 && half != *v {
                    out.push(Value::Int(half));
                }
                let step_toward_zero = if *v > 0 { *v - 1 } else { *v + 1 };
                if step_toward_zero != 0 && step_toward_zero != half {
                    out.push(Value::Int(step_toward_zero));
                }
            }
        }
        Value::Float(v) => {
            if v.abs() > 1e-9 {
                out.push(Value::Float(0.0));
                if *v < 0.0 {
                    out.push(Value::Float(-*v));
                }
                let half = (v / 2.0).trunc();
                if (half - *v).abs() > 1e-9 {
                    out.push(Value::Float(half));
                }
            }
        }
        Value::Bool(true) => {
            out.push(Value::Bool(false));
        }
        Value::Str(s) => {
            if !s.is_empty() {
                out.push(Value::Str(String::new()));
                let chars: Vec<char> = s.chars().collect();
                if chars.len() > 1 {
                    let mid = chars.len() / 2;
                    out.push(Value::Str(chars[..mid].iter().collect()));
                    out.push(Value::Str(chars[mid..].iter().collect()));
                }
                for i in 0..chars.len().min(8) {
                    let mut c = chars.clone();
                    c.remove(i);
                    out.push(Value::Str(c.into_iter().collect()));
                }
            }
        }
        Value::List(items) => {
            if !items.is_empty() {
                out.push(Value::List(Vec::new()));
                if items.len() > 1 {
                    let mid = items.len() / 2;
                    out.push(Value::List(items[..mid].to_vec()));
                    out.push(Value::List(items[mid..].to_vec()));
                }
                // Try removing one element at a time
                for i in 0..items.len().min(12) {
                    let mut shorter = items.clone();
                    shorter.remove(i);
                    out.push(Value::List(shorter));
                }
                // Try shrinking individual elements in place
                for i in 0..items.len().min(8) {
                    for elem_cand in shrink_value_candidates(&items[i]) {
                        let mut mutated = items.clone();
                        mutated[i] = elem_cand;
                        out.push(Value::List(mutated));
                    }
                }
            }
        }
        Value::Struct { name, fields } => {
            for (k, fv) in fields {
                for cand in shrink_value_candidates(fv) {
                    let mut next_fields = fields.clone();
                    next_fields.insert(k.clone(), cand);
                    out.push(Value::Struct {
                        name: name.clone(),
                        fields: next_fields,
                    });
                }
            }
        }
        _ => {}
    }
    out
}

fn infer_invariants(
    f: &FnDecl,
    hub: &HubModule,
    observations: &[(Vec<Value>, Value)],
) -> Vec<String> {
    let mut invs = Vec::new();
    if observations.is_empty() {
        return invs;
    }

    if f.ret_ty != Type::Void {
        invs.push(format!(
            "Total & Crash-Free across {} generated trial(s)",
            observations.len()
        ));
    }

    match &f.ret_ty {
        Type::Int => {
            let rets: Vec<i64> = observations
                .iter()
                .filter_map(|(_, r)| match r {
                    Value::Int(v) => Some(*v),
                    _ => None,
                })
                .collect();
            if rets.len() >= 2 {
                if rets.iter().all(|&v| v >= 0) {
                    invs.push("Non-Negative Output: result >= 0".to_string());
                }
                for (p_idx, param) in f.params.iter().enumerate() {
                    if param.ty == Type::Int {
                        let mut always_ge = true;
                        let mut always_le = true;
                        for (args, r) in observations {
                            if let (Some(Value::Int(pv)), Value::Int(rv)) = (args.get(p_idx), r) {
                                if *rv < *pv {
                                    always_ge = false;
                                }
                                if *rv > *pv {
                                    always_le = false;
                                }
                            }
                        }
                        if always_ge {
                            invs.push(format!("Lower-Bounded by Parameter: result >= {}", param.name));
                        } else if always_le {
                            invs.push(format!("Upper-Bounded by Parameter: result <= {}", param.name));
                        }
                    }
                }
            }
        }
        Type::List(_) => {
            for (p_idx, param) in f.params.iter().enumerate() {
                if matches!(param.ty, Type::List(_)) {
                    let mut eq_len = true;
                    let mut le_len = true;
                    for (args, r) in observations {
                        if let (Some(Value::List(in_l)), Value::List(out_l)) = (args.get(p_idx), r)
                        {
                            if out_l.len() != in_l.len() {
                                eq_len = false;
                            }
                            if out_l.len() > in_l.len() {
                                le_len = false;
                            }
                        }
                    }
                    if eq_len {
                        invs.push(format!(
                            "Length-Preserving Map: len(result) == len({})",
                            param.name
                        ));
                    } else if le_len {
                        invs.push(format!(
                            "Contractive / Filter Output: len(result) <= len({})",
                            param.name
                        ));
                    }
                }
            }
        }
        Type::Named(struct_name) => {
            if let Some(st) = hub.find_struct(struct_name) {
                let int_fields: Vec<&str> = st
                    .fields
                    .iter()
                    .filter(|fld| fld.ty == Type::Int)
                    .map(|fld| fld.name.as_str())
                    .collect();
                for &fname in &int_fields {
                    let all_non_neg = observations.iter().all(|(_, r)| match r {
                        Value::Struct { fields, .. } => {
                            matches!(fields.get(fname), Some(Value::Int(v)) if *v >= 0)
                        }
                        _ => false,
                    });
                    if all_non_neg {
                        invs.push(format!("Non-Negative Field: result.{} >= 0", fname));
                    }
                }
                // Check conservation law: `result.f1 + result.f2 == len(list_param)`
                if int_fields.len() >= 2 {
                    for (p_idx, param) in f.params.iter().enumerate() {
                        if matches!(param.ty, Type::List(_)) {
                            for i in 0..int_fields.len() {
                                for j in (i + 1)..int_fields.len() {
                                    let f1 = int_fields[i];
                                    let f2 = int_fields[j];
                                    let conserved = observations.iter().all(|(args, r)| {
                                        if let (
                                            Some(Value::List(items)),
                                            Value::Struct { fields, .. },
                                        ) = (args.get(p_idx), r)
                                        {
                                            if let (Some(Value::Int(v1)), Some(Value::Int(v2))) =
                                                (fields.get(f1), fields.get(f2))
                                            {
                                                return v1.checked_add(*v2)
                                                    == Some(items.len() as i64);
                                            }
                                        }
                                        false
                                    });
                                    if conserved {
                                        invs.push(format!(
                                            "Conservation Law: result.{} + result.{} == len({})",
                                            f1, f2, param.name
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        _ => {}
    }

    invs
}

fn synthesize_trial_args(
    f: &FnDecl,
    hub: &HubModule,
    seed_args: Option<&Vec<Value>>,
    trial_idx: usize,
    rng: &mut QcRng,
) -> Vec<Value> {
    if trial_idx == 0 {
        if let Some(sa) = seed_args {
            if sa.len() == f.params.len() {
                return sa.clone();
            }
        }
    }

    let mut out = Vec::with_capacity(f.params.len());
    for (p_idx, param) in f.params.iter().enumerate() {
        let seed_val = seed_args.and_then(|sa| sa.get(p_idx));
        out.push(gen_value_for_type(
            &param.ty,
            &param.name,
            hub,
            seed_val,
            trial_idx,
            rng,
        ));
    }
    out
}

fn gen_value_for_type(
    ty: &Type,
    param_name: &str,
    hub: &HubModule,
    seed_val: Option<&Value>,
    trial_idx: usize,
    rng: &mut QcRng,
) -> Value {
    match ty {
        Type::Int => {
            let min_pos = param_name.contains("window")
                || param_name.contains("cap")
                || param_name.contains("base")
                || param_name.contains("limit")
                || param_name.contains("budget")
                || param_name.contains("max")
                || matches!(seed_val, Some(Value::Int(v)) if *v > 0);
            if min_pos {
                Value::Int(rng.range_i64(1, 500))
            } else {
                match trial_idx % 6 {
                    0 => Value::Int(0),
                    1 => Value::Int(1),
                    2 => Value::Int(rng.range_i64(1, 250)),
                    _ => Value::Int(rng.range_i64(-50, 600)),
                }
            }
        }
        Type::Float => Value::Float((rng.range_i64(0, 400) as f64) / 2.0),
        Type::Bool => Value::Bool(rng.next_u64().is_multiple_of(2)),
        Type::Str => {
            if let Some(Value::Str(s)) = seed_val {
                if trial_idx.is_multiple_of(2) {
                    return Value::Str(s.clone());
                }
            }
            let pool = ["alpha", "beta", "ok", "warn", "service_a", "req_1"];
            Value::Str(pool[(rng.next_u64() as usize) % pool.len()].to_string())
        }
        Type::Void => Value::Void,
        Type::List(inner) => {
            let len = (rng.next_u64() as usize % 7) + 1;
            let mut items = Vec::with_capacity(len);
            let seed_elem = match seed_val {
                Some(Value::List(v)) => v.first(),
                _ => None,
            };
            for i in 0..len {
                items.push(gen_value_for_type(
                    inner,
                    param_name,
                    hub,
                    seed_elem,
                    trial_idx + i,
                    rng,
                ));
            }
            Value::List(items)
        }
        Type::Named(name) => {
            if let Some(en) = hub.find_enum(name) {
                let idx = (rng.next_u64() as usize) % en.variants.len().max(1);
                Value::EnumVariant {
                    enum_name: name.clone(),
                    variant: en.variants.get(idx).cloned().unwrap_or_default(),
                }
            } else if let Some(st) = hub.find_struct(name) {
                let mut fields = BTreeMap::new();
                for fld in &st.fields {
                    let f_seed = match seed_val {
                        Some(Value::Struct { fields: sf, .. }) => sf.get(&fld.name),
                        _ => None,
                    };
                    fields.insert(
                        fld.name.clone(),
                        gen_value_for_type(&fld.ty, &fld.name, hub, f_seed, trial_idx, rng),
                    );
                }
                Value::Struct {
                    name: name.clone(),
                    fields,
                }
            } else {
                default_value_for_type(ty, hub, trial_idx)
            }
        }
    }
}

fn format_value_tuple(args: &[Value]) -> String {
    let parts: Vec<String> = args.iter().map(|v| v.display_str()).collect();
    format!("({})", parts.join(", "))
}

fn value_to_hub_expr(val: &Value) -> Expr {
    match val {
        Value::Int(v) => {
            if *v < 0 && *v > i64::MIN {
                Expr::Unary {
                    op: crate::hub::UnaryOp::Neg,
                    expr: Box::new(Expr::Int(-*v)),
                }
            } else {
                Expr::Int(*v)
            }
        }
        Value::Float(v) => {
            if *v < 0.0 {
                Expr::Unary {
                    op: crate::hub::UnaryOp::Neg,
                    expr: Box::new(Expr::Float(-*v)),
                }
            } else {
                Expr::Float(*v)
            }
        }
        Value::Bool(b) => Expr::Bool(*b),
        Value::Str(s) => Expr::Str(s.clone()),
        Value::List(items) => Expr::List(items.iter().map(value_to_hub_expr).collect()),
        Value::EnumVariant { enum_name, variant } => Expr::EnumVariant {
            enum_name: enum_name.clone(),
            variant: variant.clone(),
        },
        Value::Struct { name, fields } => Expr::StructInit {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(k, v)| (k.clone(), value_to_hub_expr(v)))
                .collect(),
        },
        Value::Void => Expr::Int(0),
    }
}

pub(crate) fn format_repro_across_spokes(
    hub: &HubModule,
    fn_name: &str,
    args: &[Value],
) -> BTreeMap<String, String> {
    let mut mini = HubModule::new();
    for item in &hub.items {
        if matches!(item, Item::Struct(_) | Item::Enum(_)) {
            mini.items.push(item.clone());
        }
    }
    let call_expr = Expr::Call {
        func: fn_name.to_string(),
        args: args.iter().map(value_to_hub_expr).collect(),
    };
    mini.items.push(Item::Test(TestDecl {
        id: 1,
        name: "minimized_counterexample".to_string(),
        body: vec![Stmt::Expr {
            id: 2,
            expr: call_expr,
            meta: Metadata::new(),
        }],
        comments: Vec::new(),
        meta: Metadata::new(),
    }));
    crate::hub::normalize_module(&mut mini);

    let mut out = BTreeMap::new();
    let needle_paren = format!("{}(", fn_name);
    let needle_sexpr = format!("(call {}", fn_name);
    for spoke in SpokeId::ALL {
        let projected = lens_for(spoke).get(&mini);
        let call_line = projected
            .lines()
            .map(str::trim)
            .find(|l| {
                (l.contains(&needle_paren) || l.contains(&needle_sexpr))
                    && !l.starts_with("fn ")
                    && !l.starts_with("sub ")
            })
            .unwrap_or("")
            .to_string();
        out.insert(spoke.as_str().to_string(), call_line);
    }
    out
}

struct QcRng {
    state: u64,
}

impl QcRng {
    fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 { 0x9E37_79B9_7F4A_7C15 } else { seed },
        }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        if hi <= lo {
            return lo;
        }
        let span = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + ((self.next_u64() as u128) % span) as i128) as i64
    }
}

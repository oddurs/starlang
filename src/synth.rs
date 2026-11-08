use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::time::Instant;

use crate::eval::{eval_fn_with_values, eval_tests_default, Value};
use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, Metadata, Param, Stmt,
    TestDecl, Type, UnaryOp,
};
use crate::lens::SpokeId;
use crate::spokes::lens_for;
use crate::typecheck::check_module;
use crate::verify::verify_module;

#[derive(Debug, Clone)]
pub struct IoExample {
    pub args: Vec<Value>,
    pub expected: Value,
}

#[derive(Debug, Clone)]
pub struct SynthSpec {
    pub fn_name: String,
    pub params: Vec<(String, Type)>,
    pub ret_ty: Type,
    pub examples: Vec<IoExample>,
}

#[derive(Debug, Clone)]
pub struct SynthReport {
    pub ok: bool,
    pub fn_name: String,
    pub signature: String,
    pub examples_count: usize,
    pub candidates_explored: usize,
    pub pruned_by_obs_equiv: usize,
    pub ast_nodes: usize,
    pub safety_proven: bool,
    pub tests_passed: bool,
    pub elapsed_ms: u128,
    pub program_summary: String,
    pub synthesized_fn: Option<FnDecl>,
    pub synthesized_test: Option<TestDecl>,
    pub views_by_spoke: BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct CfgBasicBlock {
    pub id: usize,
    pub label: String,
    pub kind: String,
    pub stmts: Vec<String>,
    pub successors: Vec<(usize, String)>,
    pub predecessors: Vec<usize>,
    pub dominators: Vec<usize>,
}

#[derive(Debug, Clone)]
pub struct FunctionCfg {
    pub fn_name: String,
    pub signature: String,
    pub blocks: Vec<CfgBasicBlock>,
    pub back_edges: Vec<(usize, usize)>,
    pub natural_loops: usize,
    pub mermaid: String,
    pub dot: String,
}

#[derive(Debug, Clone)]
pub struct ModuleCfgReport {
    pub total_functions: usize,
    pub total_blocks: usize,
    pub total_edges: usize,
    pub total_natural_loops: usize,
    pub functions: Vec<FunctionCfg>,
    pub module_mermaid: String,
    pub module_dot: String,
}

/// Built-in default Programming-by-Example (PBE) synthesis specification:
/// Synthesizes `clamp_bonus(score: Int, cap: Int) -> Int` from 4 input/output pairs:
///   (40, 100) => 80
///   (75, 100) => 100
///   (-15, 60) => 0
///   (0, 50)   => 0
/// Target law: `max(0, min(score * 2, cap))`
pub fn default_synth_spec() -> SynthSpec {
    SynthSpec {
        fn_name: "clamp_bonus".to_string(),
        params: vec![
            ("score".to_string(), Type::Int),
            ("cap".to_string(), Type::Int),
        ],
        ret_ty: Type::Int,
        examples: vec![
            IoExample {
                args: vec![Value::Int(40), Value::Int(100)],
                expected: Value::Int(80),
            },
            IoExample {
                args: vec![Value::Int(75), Value::Int(100)],
                expected: Value::Int(100),
            },
            IoExample {
                args: vec![Value::Int(-15), Value::Int(60)],
                expected: Value::Int(0),
            },
            IoExample {
                args: vec![Value::Int(0), Value::Int(50)],
                expected: Value::Int(0),
            },
        ],
    }
}

/// Built-in list-folding Programming-by-Example specification:
/// Synthesizes `sum_above(items: List<Int>, floor: Int) -> Int` from 3 I/O examples:
///   ([10, 5, 25, 8], 9) => 35
///   ([2, 3, 4], 10)     => 0
///   ([15, 20, 3], 10)   => 35
pub fn default_list_synth_spec() -> SynthSpec {
    SynthSpec {
        fn_name: "sum_above".to_string(),
        params: vec![
            ("items".to_string(), Type::list(Type::Int)),
            ("floor".to_string(), Type::Int),
        ],
        ret_ty: Type::Int,
        examples: vec![
            IoExample {
                args: vec![
                    Value::List(vec![
                        Value::Int(10),
                        Value::Int(5),
                        Value::Int(25),
                        Value::Int(8),
                    ]),
                    Value::Int(9),
                ],
                expected: Value::Int(35),
            },
            IoExample {
                args: vec![
                    Value::List(vec![Value::Int(2), Value::Int(3), Value::Int(4)]),
                    Value::Int(10),
                ],
                expected: Value::Int(0),
            },
            IoExample {
                args: vec![
                    Value::List(vec![Value::Int(15), Value::Int(20), Value::Int(3)]),
                    Value::Int(10),
                ],
                expected: Value::Int(35),
            },
        ],
    }
}

/// Parse a compact PBE specification string such as:
///   `clamp_bonus(score: Int, cap: Int) -> Int | (40, 100) => 80; (75, 100) => 100; (-15, 60) => 0`
/// or preset names `"clamp_bonus"` / `"sum_above"`.
pub fn parse_synth_spec(spec_str: &str) -> Result<SynthSpec, String> {
    let trimmed = spec_str.trim();
    if trimmed.is_empty() || trimmed == "clamp_bonus" || trimmed == "default" {
        return Ok(default_synth_spec());
    }
    if trimmed == "sum_above" || trimmed == "list" {
        return Ok(default_list_synth_spec());
    }

    let (sig_part, ex_part) = trimmed
        .split_once('|')
        .ok_or_else(|| "expected `<signature> | <examples>` separated by '|'".to_string())?;

    let sig = sig_part.trim().strip_prefix("fn ").unwrap_or(sig_part.trim());
    let lparen = sig
        .find('(')
        .ok_or_else(|| "expected '(' in function signature".to_string())?;
    let rparen = sig
        .find(')')
        .ok_or_else(|| "expected ')' in function signature".to_string())?;
    let fn_name = sig[..lparen].trim().to_string();
    let params_raw = &sig[lparen + 1..rparen];
    let mut params = Vec::new();
    for p_piece in params_raw.split(',') {
        let p_piece = p_piece.trim();
        if p_piece.is_empty() {
            continue;
        }
        let (pname, pty_str) = p_piece
            .split_once(':')
            .ok_or_else(|| format!("expected `name: Type` in parameter `{}`", p_piece))?;
        params.push((pname.trim().to_string(), parse_simple_type(pty_str.trim())?));
    }

    let after_rparen = sig[rparen + 1..].trim();
    let ret_ty = if let Some(r) = after_rparen.strip_prefix("->") {
        parse_simple_type(r.trim())?
    } else {
        Type::Int
    };

    let mut examples = Vec::new();
    for ex_raw in ex_part.split(';') {
        let ex_raw = ex_raw.trim();
        if ex_raw.is_empty() {
            continue;
        }
        let (lhs, rhs) = ex_raw
            .split_once("=>")
            .ok_or_else(|| format!("expected `(args) => expected` in `{}`", ex_raw))?;
        let args = parse_value_tuple(lhs.trim(), &params)?;
        let expected = parse_single_value(rhs.trim(), &ret_ty)?;
        examples.push(IoExample { args, expected });
    }

    if examples.is_empty() {
        return Err("at least 1 input/output example is required".to_string());
    }

    Ok(SynthSpec {
        fn_name,
        params,
        ret_ty,
        examples,
    })
}

fn parse_simple_type(s: &str) -> Result<Type, String> {
    match s {
        "Int" | "i64" | "int" => Ok(Type::Int),
        "Float" | "f64" | "float" => Ok(Type::Float),
        "Bool" | "bool" => Ok(Type::Bool),
        "Str" | "String" | "str" => Ok(Type::Str),
        "List<Int>" | "List[Int]" | "[Int]" => Ok(Type::list(Type::Int)),
        other => Err(format!("unsupported synthesis type `{}`", other)),
    }
}

fn parse_value_tuple(raw: &str, params: &[(String, Type)]) -> Result<Vec<Value>, String> {
    let inner = raw
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(raw)
        .trim();
    // Split top-level commas (respecting `[...]`)
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, ch) in inner.char_indices() {
        match ch {
            '[' => depth += 1,
            ']' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(inner[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    if start <= inner.len() {
        let tail = inner[start..].trim();
        if !tail.is_empty() {
            parts.push(tail);
        }
    }
    if parts.len() != params.len() {
        return Err(format!(
            "expected {} argument(s), got {} in `{}`",
            params.len(),
            parts.len(),
            raw
        ));
    }
    let mut out = Vec::with_capacity(params.len());
    for (piece, (_, ty)) in parts.into_iter().zip(params.iter()) {
        out.push(parse_single_value(piece, ty)?);
    }
    Ok(out)
}

fn parse_single_value(raw: &str, ty: &Type) -> Result<Value, String> {
    let t = raw.trim();
    match ty {
        Type::Int => t
            .parse::<i64>()
            .map(Value::Int)
            .map_err(|_| format!("invalid Int `{}`", t)),
        Type::Float => t
            .parse::<f64>()
            .map(Value::Float)
            .map_err(|_| format!("invalid Float `{}`", t)),
        Type::Bool => match t {
            "true" => Ok(Value::Bool(true)),
            "false" => Ok(Value::Bool(false)),
            _ => Err(format!("invalid Bool `{}`", t)),
        },
        Type::Str => Ok(Value::Str(t.trim_matches('"').to_string())),
        Type::List(elem_ty) => {
            let body = t
                .strip_prefix('[')
                .and_then(|s| s.strip_suffix(']'))
                .ok_or_else(|| format!("expected `[...]` list literal, got `{}`", t))?
                .trim();
            if body.is_empty() {
                return Ok(Value::List(Vec::new()));
            }
            let mut items = Vec::new();
            for item_str in body.split(',') {
                items.push(parse_single_value(item_str.trim(), elem_ty)?);
            }
            Ok(Value::List(items))
        }
        _ => Err("unsupported value type in PBE parser".to_string()),
    }
}

/// Run Bottom-Up Observational-Equivalence Inductive Program Synthesis (PBE) on `spec`.
pub fn synthesize_from_examples(spec: &SynthSpec) -> SynthReport {
    let start = Instant::now();
    let params_sig: Vec<String> = spec
        .params
        .iter()
        .map(|(n, t)| format!("{}: {}", n, t.display()))
        .collect();
    let signature = format!(
        "fn {}({}) -> {}",
        spec.fn_name,
        params_sig.join(", "),
        spec.ret_ty.display()
    );

    let mut candidates_explored = 0usize;
    let mut pruned_by_obs_equiv = 0usize;

    let has_list_param = spec
        .params
        .iter()
        .any(|(_, ty)| matches!(ty, Type::List(_)));

    let found_body: Option<(Vec<Stmt>, String)> = if has_list_param {
        synthesize_list_fold_program(spec, &mut candidates_explored)
    } else {
        synthesize_scalar_program(spec, &mut candidates_explored, &mut pruned_by_obs_equiv)
    };

    let Some((body, program_summary)) = found_body else {
        return SynthReport {
            ok: false,
            fn_name: spec.fn_name.clone(),
            signature,
            examples_count: spec.examples.len(),
            candidates_explored,
            pruned_by_obs_equiv,
            ast_nodes: 0,
            safety_proven: false,
            tests_passed: false,
            elapsed_ms: start.elapsed().as_millis(),
            program_summary: "(no matching program found within search depth)".to_string(),
            synthesized_fn: None,
            synthesized_test: None,
            views_by_spoke: BTreeMap::new(),
        };
    };

    let fn_decl = FnDecl {
        id: 1,
        name: spec.fn_name.clone(),
        params: spec
            .params
            .iter()
            .enumerate()
            .map(|(i, (n, t))| Param {
                id: (i + 2) as u64,
                name: n.clone(),
                ty: t.clone(),
                meta: Metadata::new(),
            })
            .collect(),
        ret_ty: spec.ret_ty.clone(),
        body,
        comments: vec![format!(
            "Synthesized by StarLang PBE from {} I/O example(s)",
            spec.examples.len()
        )],
        meta: Metadata::new(),
    };

    let test_decl = build_synth_unit_test(spec);
    let mut synth_hub = HubModule {
        items: vec![
            Item::Function(fn_decl.clone()),
            Item::Test(test_decl.clone()),
        ],
        next_id: 100,
    };
    let ast_nodes = synth_hub.node_count();
    let type_ok = check_module(&synth_hub).is_empty();
    let test_res = eval_tests_default(&synth_hub);
    let tests_passed = type_ok && !test_res.is_empty() && test_res.iter().all(|t| t.passed);
    let ver = verify_module(&synth_hub);
    let safety_proven = ver.refuted == 0;

    // Also add a `main()` calling the first example so standalone spokes print a live preview
    if let Some(first_ex) = spec.examples.first() {
        let call_expr = Expr::Call {
            func: spec.fn_name.clone(),
            args: first_ex.args.iter().map(val_to_expr).collect(),
        };
        synth_hub.items.insert(
            1,
            Item::Function(FnDecl {
                id: 50,
                name: "main".to_string(),
                params: Vec::new(),
                ret_ty: Type::Void,
                body: vec![Stmt::Expr {
                    id: 51,
                    expr: Expr::Intrinsic(Box::new(Intrinsic::Print(vec![
                        Expr::Str(format!("{}:", spec.fn_name)),
                        call_expr,
                    ]))),
                    meta: Metadata::new(),
                }],
                comments: Vec::new(),
                meta: Metadata::new(),
            }),
        );
    }
    crate::hub::normalize_module(&mut synth_hub);

    let mut views_by_spoke = BTreeMap::new();
    for spoke in SpokeId::ALL {
        views_by_spoke.insert(spoke.as_str().to_string(), lens_for(spoke).get(&synth_hub));
    }

    SynthReport {
        ok: tests_passed && safety_proven,
        fn_name: spec.fn_name.clone(),
        signature,
        examples_count: spec.examples.len(),
        candidates_explored,
        pruned_by_obs_equiv,
        ast_nodes,
        safety_proven,
        tests_passed,
        elapsed_ms: start.elapsed().as_millis(),
        program_summary,
        synthesized_fn: Some(fn_decl),
        synthesized_test: Some(test_decl),
        views_by_spoke,
    }
}

fn synthesize_scalar_program(
    spec: &SynthSpec,
    explored: &mut usize,
    pruned: &mut usize,
) -> Option<(Vec<Stmt>, String)> {
    let expected_vec: Vec<Value> = spec.examples.iter().map(|e| e.expected.clone()).collect();
    let mut pool: Vec<(Expr, String, Vec<Value>)> = Vec::new();
    let mut seen_vecs: HashMap<String, usize> = HashMap::new();

    // Seed level-0 atoms: parameters + constants
    let mut atoms: Vec<(Expr, String)> = Vec::new();
    for (pname, pty) in &spec.params {
        if *pty == Type::Int {
            atoms.push((Expr::Var(pname.clone()), pname.clone()));
        }
    }
    let mut const_set: BTreeSet<i64> = [0, 1, 2, -1, 10, 100].into_iter().collect();
    for ex in &spec.examples {
        if let Value::Int(v) = ex.expected {
            const_set.insert(v);
        }
    }
    for c in const_set {
        atoms.push((Expr::Int(c), c.to_string()));
    }

    for (expr, label) in atoms {
        *explored += 1;
        if let Some(sig_vec) = eval_expr_on_examples(&expr, spec) {
            if sig_vec == expected_vec {
                return Some((
                    vec![Stmt::Return {
                        id: 10,
                        value: Some(expr),
                        meta: Metadata::new(),
                    }],
                    format!("return {}", label),
                ));
            }
            let key = format!("{:?}", sig_vec);
            if let std::collections::hash_map::Entry::Vacant(e) = seen_vecs.entry(key) {
                e.insert(pool.len());
                pool.push((expr, label, sig_vec));
            } else {
                *pruned += 1;
            }
        }
    }

    // Enumerate depth 1..=3 expressions with direct vector evaluation + observational-equivalence pruning
    for depth in 1..=3 {
        let cur_len = pool.len();
        let mut next_items: Vec<(Expr, String, Vec<Value>)> = Vec::new();

        // Unary `abs(x)` and `-x`
        for idx in 0..cur_len {
            let (ref e1, ref l1, ref v1) = pool[idx];
            for (is_abs, cand_e, cand_l) in [
                (
                    true,
                    Expr::Intrinsic(Box::new(Intrinsic::Abs(e1.clone()))),
                    format!("abs({})", l1),
                ),
                (
                    false,
                    Expr::Unary {
                        op: UnaryOp::Neg,
                        expr: Box::new(e1.clone()),
                    },
                    format!("-({})", l1),
                ),
            ] {
                *explored += 1;
                let sig_vec: Vec<Value> = v1
                    .iter()
                    .map(|val| match val {
                        Value::Int(n) => Value::Int(if is_abs { n.saturating_abs() } else { n.saturating_neg() }),
                        _ => Value::Int(0),
                    })
                    .collect();
                if sig_vec == expected_vec {
                    return Some((
                        vec![Stmt::Return {
                            id: 10,
                            value: Some(cand_e),
                            meta: Metadata::new(),
                        }],
                        format!("return {}", cand_l),
                    ));
                }
                let key = format!("{:?}", sig_vec);
                if let std::collections::hash_map::Entry::Vacant(e) = seen_vecs.entry(key) {
                    if depth < 3 {
                        e.insert(pool.len() + next_items.len());
                        next_items.push((cand_e, cand_l, sig_vec));
                    }
                } else {
                    *pruned += 1;
                }
            }
        }

        // Binary `+`, `-`, `*`, `min`, `max`
        for i in 0..cur_len {
            for j in 0..cur_len {
                let (ref e1, ref l1, ref v1) = pool[i];
                let (ref e2, ref l2, ref v2) = pool[j];
                if matches!(e1, Expr::Int(_)) && matches!(e2, Expr::Int(_)) {
                    continue;
                }
                let ops: &[(&str, bool)] = &[
                    ("add", true),
                    ("mul", true),
                    ("min", true),
                    ("max", true),
                    ("sub", false),
                ];
                for &(op_kind, commutative) in ops {
                    if commutative && i > j {
                        continue;
                    }
                    *explored += 1;
                    let sig_vec: Vec<Value> = v1
                        .iter()
                        .zip(v2.iter())
                        .map(|(a, b)| match (a, b) {
                            (Value::Int(x), Value::Int(y)) => Value::Int(match op_kind {
                                "add" => x.saturating_add(*y),
                                "mul" => x.saturating_mul(*y),
                                "min" => (*x).min(*y),
                                "max" => (*x).max(*y),
                                _ => x.saturating_sub(*y),
                            }),
                            _ => Value::Int(0),
                        })
                        .collect();

                    let build_cand = || -> (Expr, String) {
                        match op_kind {
                            "add" => (
                                Expr::Binary {
                                    op: BinOp::Add,
                                    left: Box::new(e1.clone()),
                                    right: Box::new(e2.clone()),
                                },
                                format!("({} + {})", l1, l2),
                            ),
                            "mul" => (
                                Expr::Binary {
                                    op: BinOp::Mul,
                                    left: Box::new(e1.clone()),
                                    right: Box::new(e2.clone()),
                                },
                                format!("({} * {})", l1, l2),
                            ),
                            "min" => (
                                Expr::Intrinsic(Box::new(Intrinsic::Min(e1.clone(), e2.clone()))),
                                format!("min({}, {})", l1, l2),
                            ),
                            "max" => (
                                Expr::Intrinsic(Box::new(Intrinsic::Max(e1.clone(), e2.clone()))),
                                format!("max({}, {})", l1, l2),
                            ),
                            _ => (
                                Expr::Binary {
                                    op: BinOp::Sub,
                                    left: Box::new(e1.clone()),
                                    right: Box::new(e2.clone()),
                                },
                                format!("({} - {})", l1, l2),
                            ),
                        }
                    };

                    if sig_vec == expected_vec {
                        let (cand_e, cand_l) = build_cand();
                        return Some((
                            vec![Stmt::Return {
                                id: 10,
                                value: Some(cand_e),
                                meta: Metadata::new(),
                            }],
                            format!("return {}", cand_l),
                        ));
                    }
                    let key = format!("{:?}", sig_vec);
                    if let std::collections::hash_map::Entry::Vacant(e) = seen_vecs.entry(key) {
                        if depth < 3 && next_items.len() < 160 {
                            let (cand_e, cand_l) = build_cand();
                            e.insert(pool.len() + next_items.len());
                            next_items.push((cand_e, cand_l, sig_vec));
                        }
                    } else {
                        *pruned += 1;
                    }
                }
            }
        }

        pool.extend(next_items);
    }

    // Phase 1b: Conditional `if (cond) { return e_then; } else { return e_else; }`
    for i in 0..pool.len().min(40) {
        for j in 0..pool.len().min(40) {
            if i == j {
                continue;
            }
            let (ref t_expr, ref t_lbl, ref t_vec) = pool[i];
            let (ref f_expr, ref f_lbl, ref f_vec) = pool[j];
            // Check if every example output is covered by either `t_vec[k]` or `f_vec[k]`
            if !expected_vec
                .iter()
                .enumerate()
                .all(|(k, exp)| &t_vec[k] == exp || &f_vec[k] == exp)
            {
                continue;
            }
            // Search for a relational predicate `a op b` that selects `t_vec` vs `f_vec`
            for a_idx in 0..pool.len().min(20) {
                for b_idx in 0..pool.len().min(20) {
                    if a_idx == b_idx {
                        continue;
                    }
                    let (ref lhs, ref l_lbl, ref l_vec) = pool[a_idx];
                    let (ref rhs, ref r_lbl, ref r_vec) = pool[b_idx];
                    for (op, op_str) in [
                        (BinOp::Gt, ">"),
                        (BinOp::Ge, ">="),
                        (BinOp::Lt, "<"),
                        (BinOp::Le, "<="),
                        (BinOp::Eq, "=="),
                    ] {
                        *explored += 1;
                        let matches_all = (0..expected_vec.len()).all(|k| {
                            let (Value::Int(lv), Value::Int(rv)) = (&l_vec[k], &r_vec[k]) else {
                                return false;
                            };
                            let b = match op {
                                BinOp::Gt => lv > rv,
                                BinOp::Ge => lv >= rv,
                                BinOp::Lt => lv < rv,
                                BinOp::Le => lv <= rv,
                                BinOp::Eq => lv == rv,
                                _ => false,
                            };
                            let chosen = if b { &t_vec[k] } else { &f_vec[k] };
                            chosen == &expected_vec[k]
                        });
                        if matches_all {
                            let cond_expr = Expr::Binary {
                                op,
                                left: Box::new(lhs.clone()),
                                right: Box::new(rhs.clone()),
                            };
                            let stmts = vec![Stmt::If {
                                id: 10,
                                cond: cond_expr,
                                then_body: vec![Stmt::Return {
                                    id: 11,
                                    value: Some(t_expr.clone()),
                                    meta: Metadata::new(),
                                }],
                                else_body: vec![Stmt::Return {
                                    id: 12,
                                    value: Some(f_expr.clone()),
                                    meta: Metadata::new(),
                                }],
                                meta: Metadata::new(),
                            }];
                            let summary = format!(
                                "if ({} {} {}) {{ return {}; }} else {{ return {}; }}",
                                l_lbl, op_str, r_lbl, t_lbl, f_lbl
                            );
                            return Some((stmts, summary));
                        }
                    }
                }
            }
        }
    }

    None
}

fn synthesize_list_fold_program(
    spec: &SynthSpec,
    explored: &mut usize,
) -> Option<(Vec<Stmt>, String)> {
    let list_param = spec
        .params
        .iter()
        .find(|(_, ty)| matches!(ty, Type::List(_)))?
        .0
        .clone();
    let scalar_params: Vec<String> = spec
        .params
        .iter()
        .filter(|(_, ty)| *ty == Type::Int)
        .map(|(n, _)| n.clone())
        .collect();

    let mut bounds: Vec<(Expr, String)> = vec![(Expr::Int(0), "0".to_string())];
    for sp in &scalar_params {
        bounds.push((Expr::Var(sp.clone()), sp.clone()));
    }

    let accum_terms: Vec<(Expr, String)> = vec![
        (Expr::Var("item".to_string()), "item".to_string()),
        (Expr::Int(1), "1".to_string()),
    ];

    type FoldPred = (Option<(BinOp, Expr, String)>, String);
    let preds: Vec<FoldPred> = {
        let mut v = vec![(None, "true".to_string())];
        for (b_expr, b_lbl) in &bounds {
            for (op, sym) in [
                (BinOp::Gt, ">"),
                (BinOp::Ge, ">="),
                (BinOp::Lt, "<"),
                (BinOp::Le, "<="),
                (BinOp::Eq, "=="),
            ] {
                v.push((
                    Some((op, b_expr.clone(), b_lbl.clone())),
                    format!("item {} {}", sym, b_lbl),
                ));
            }
        }
        v
    };

    for (term_expr, term_lbl) in &accum_terms {
        for (pred_opt, pred_lbl) in &preds {
            *explored += 1;
            let loop_stmt = if let Some((op, rhs_expr, _)) = pred_opt {
                Stmt::If {
                    id: 12,
                    cond: Expr::Binary {
                        op: *op,
                        left: Box::new(Expr::Var("item".to_string())),
                        right: Box::new(rhs_expr.clone()),
                    },
                    then_body: vec![Stmt::Assign {
                        id: 13,
                        target: AssignTarget::Var("acc".to_string()),
                        op: AssignOp::AddAssign,
                        value: term_expr.clone(),
                        meta: Metadata::new(),
                    }],
                    else_body: Vec::new(),
                    meta: Metadata::new(),
                }
            } else {
                Stmt::Assign {
                    id: 12,
                    target: AssignTarget::Var("acc".to_string()),
                    op: AssignOp::AddAssign,
                    value: term_expr.clone(),
                    meta: Metadata::new(),
                }
            };

            let body = vec![
                Stmt::Let {
                    id: 10,
                    name: "acc".to_string(),
                    mutable: true,
                    ty: Some(Type::Int),
                    value: Expr::Int(0),
                    meta: Metadata::new(),
                },
                Stmt::ForEach {
                    id: 11,
                    var: "item".to_string(),
                    iter: Expr::Var(list_param.clone()),
                    body: vec![loop_stmt],
                    meta: Metadata::new(),
                },
                Stmt::Return {
                    id: 14,
                    value: Some(Expr::Var("acc".to_string())),
                    meta: Metadata::new(),
                },
            ];

            if check_body_on_examples(&body, spec) {
                let summary = format!(
                    "let acc = 0; for item in {} {{ if ({}) {{ acc += {}; }} }} return acc;",
                    list_param, pred_lbl, term_lbl
                );
                return Some((body, summary));
            }
        }
    }

    None
}

fn eval_expr_on_examples(expr: &Expr, spec: &SynthSpec) -> Option<Vec<Value>> {
    let body = vec![Stmt::Return {
        id: 1,
        value: Some(expr.clone()),
        meta: Metadata::new(),
    }];
    let temp_hub = HubModule {
        items: vec![Item::Function(FnDecl {
            id: 1,
            name: spec.fn_name.clone(),
            params: spec
                .params
                .iter()
                .enumerate()
                .map(|(i, (n, t))| Param {
                    id: (i + 2) as u64,
                    name: n.clone(),
                    ty: t.clone(),
                    meta: Metadata::new(),
                })
                .collect(),
            ret_ty: spec.ret_ty.clone(),
            body,
            comments: Vec::new(),
            meta: Metadata::new(),
        })],
        next_id: 10,
    };

    let mut out = Vec::with_capacity(spec.examples.len());
    for ex in &spec.examples {
        let (val, _, _) =
            eval_fn_with_values(&temp_hub, &spec.fn_name, ex.args.clone(), 500).ok()?;
        out.push(val);
    }
    Some(out)
}

fn check_body_on_examples(body: &[Stmt], spec: &SynthSpec) -> bool {
    let temp_hub = HubModule {
        items: vec![Item::Function(FnDecl {
            id: 1,
            name: spec.fn_name.clone(),
            params: spec
                .params
                .iter()
                .enumerate()
                .map(|(i, (n, t))| Param {
                    id: (i + 2) as u64,
                    name: n.clone(),
                    ty: t.clone(),
                    meta: Metadata::new(),
                })
                .collect(),
            ret_ty: spec.ret_ty.clone(),
            body: body.to_vec(),
            comments: Vec::new(),
            meta: Metadata::new(),
        })],
        next_id: 20,
    };

    for ex in &spec.examples {
        let Ok((val, _, _)) = eval_fn_with_values(&temp_hub, &spec.fn_name, ex.args.clone(), 1_000)
        else {
            return false;
        };
        if val != ex.expected {
            return false;
        }
    }
    true
}

fn build_synth_unit_test(spec: &SynthSpec) -> TestDecl {
    let mut body = Vec::with_capacity(spec.examples.len());
    for (idx, ex) in spec.examples.iter().enumerate() {
        let call = Expr::Call {
            func: spec.fn_name.clone(),
            args: ex.args.iter().map(val_to_expr).collect(),
        };
        body.push(Stmt::AssertEq {
            id: (30 + idx) as u64,
            left: call,
            right: val_to_expr(&ex.expected),
            meta: Metadata::new(),
        });
    }
    TestDecl {
        id: 25,
        name: format!("{}_examples", spec.fn_name),
        body,
        comments: Vec::new(),
        meta: Metadata::new(),
    }
}

fn val_to_expr(v: &Value) -> Expr {
    match v {
        Value::Int(n) => Expr::Int(*n),
        Value::Float(f) => Expr::Float(*f),
        Value::Bool(b) => Expr::Bool(*b),
        Value::Str(s) => Expr::Str(s.clone()),
        Value::List(items) => Expr::List(items.iter().map(val_to_expr).collect()),
        _ => Expr::Int(0),
    }
}

/// Build the Control-Flow Graph (CFG), Dominator sets, Natural Loop count, and Mermaid / Graphviz DOT
/// diagrams for all functions in `hub`.
pub fn analyze_cfg(hub: &HubModule) -> ModuleCfgReport {
    let mut functions = Vec::new();
    let mut total_blocks = 0usize;
    let mut total_edges = 0usize;
    let mut total_natural_loops = 0usize;

    let mut module_mermaid = String::from("flowchart TD\n");
    let mut module_dot = String::from("digraph StarLangCFG {\n  rankdir=TB;\n  node [shape=box, fontname=\"Menlo\"];\n");

    for item in &hub.items {
        if let Item::Function(f) = item {
            let fcfg = build_function_cfg(f);
            total_blocks += fcfg.blocks.len();
            total_edges += fcfg
                .blocks
                .iter()
                .map(|b| b.successors.len())
                .sum::<usize>();
            total_natural_loops += fcfg.natural_loops;

            module_mermaid.push_str(&format!("  subgraph fn_{}[\"fn {}()\"]\n", f.name, f.name));
            for line in fcfg.mermaid.lines().skip(1) {
                module_mermaid.push_str(&format!("  {}\n", line));
            }
            module_mermaid.push_str("  end\n");

            module_dot.push_str(&format!(
                "  subgraph cluster_{} {{\n    label=\"fn {}()\";\n",
                f.name, f.name
            ));
            for line in fcfg.dot.lines().skip(2) {
                if line.trim() != "}" {
                    module_dot.push_str(&format!("  {}\n", line));
                }
            }
            module_dot.push_str("  }\n");

            functions.push(fcfg);
        }
    }

    module_dot.push_str("}\n");

    ModuleCfgReport {
        total_functions: functions.len(),
        total_blocks,
        total_edges,
        total_natural_loops,
        functions,
        module_mermaid,
        module_dot,
    }
}

fn build_function_cfg(f: &FnDecl) -> FunctionCfg {
    let params_str: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.ty.display()))
        .collect();
    let signature = format!("fn {}({}) -> {}", f.name, params_str.join(", "), f.ret_ty.display());

    let mut builder = CfgBuilder {
        fn_name: &f.name,
        blocks: Vec::new(),
        loop_stack: Vec::new(),
    };
    let entry = builder.new_block("Entry", "entry");
    let exit = builder.new_block("Exit", "exit");
    let fallthrough = builder.lower_stmts(&f.body, entry, exit);
    if let Some(ft) = fallthrough {
        builder.add_edge(ft, exit, "ret");
    }

    // Compute predecessors
    let n = builder.blocks.len();
    for src in 0..n {
        let succs: Vec<usize> = builder.blocks[src]
            .successors
            .iter()
            .map(|(dst, _)| *dst)
            .collect();
        for dst in succs {
            if !builder.blocks[dst].predecessors.contains(&src) {
                builder.blocks[dst].predecessors.push(src);
            }
        }
    }

    // Iterative dataflow dominator algorithm: Dom(0) = {0}, Dom(v) = {v} U Intersect_{p in pred(v)} Dom(p)
    let mut doms: Vec<BTreeSet<usize>> = vec![(0..n).collect(); n];
    doms[0] = [0usize].into_iter().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for b in 1..n {
            let preds = &builder.blocks[b].predecessors;
            if preds.is_empty() {
                let single: BTreeSet<usize> = [b].into_iter().collect();
                if doms[b] != single {
                    doms[b] = single;
                    changed = true;
                }
                continue;
            }
            let mut new_dom = doms[preds[0]].clone();
            for &p in &preds[1..] {
                new_dom = new_dom.intersection(&doms[p]).copied().collect();
            }
            new_dom.insert(b);
            if new_dom != doms[b] {
                doms[b] = new_dom;
                changed = true;
            }
        }
    }

    let mut back_edges = Vec::new();
    for (idx, blk) in builder.blocks.iter_mut().enumerate() {
        blk.dominators = doms[idx].iter().copied().collect();
        for &(dst, _) in &blk.successors {
            if doms[idx].contains(&dst) {
                back_edges.push((idx, dst));
            }
        }
    }

    let mut mermaid = String::from("flowchart TD\n");
    let mut dot = String::from("digraph CFG {\n  rankdir=TB;\n");
    for blk in &builder.blocks {
        let node_id = format!("{}_BB{}", f.name, blk.id);
        let stmt_preview = if blk.stmts.is_empty() {
            blk.label.clone()
        } else {
            format!("{}: {}", blk.label, blk.stmts.join("; "))
        };
        let clean = stmt_preview.replace('"', "'");
        mermaid.push_str(&format!("  {}[\"{}\"]\n", node_id, clean));
        dot.push_str(&format!("  {} [label=\"{}\"];\n", node_id, clean));
        for (dst, edge_lbl) in &blk.successors {
            let dst_id = format!("{}_BB{}", f.name, dst);
            if edge_lbl.is_empty() {
                mermaid.push_str(&format!("  {} --> {}\n", node_id, dst_id));
                dot.push_str(&format!("  {} -> {};\n", node_id, dst_id));
            } else {
                mermaid.push_str(&format!("  {} -->|\"{}\"| {}\n", node_id, edge_lbl, dst_id));
                dot.push_str(&format!(
                    "  {} -> {} [label=\"{}\"];\n",
                    node_id, dst_id, edge_lbl
                ));
            }
        }
    }
    dot.push_str("}\n");

    let natural_loops = back_edges
        .iter()
        .map(|(_, h)| *h)
        .collect::<BTreeSet<_>>()
        .len();
    FunctionCfg {
        fn_name: f.name.clone(),
        signature,
        blocks: builder.blocks,
        back_edges,
        natural_loops,
        mermaid,
        dot,
    }
}

struct CfgBuilder<'a> {
    #[allow(dead_code)]
    fn_name: &'a str,
    blocks: Vec<CfgBasicBlock>,
    loop_stack: Vec<(usize, usize)>,
}

impl<'a> CfgBuilder<'a> {
    fn new_block(&mut self, label: &str, kind: &str) -> usize {
        let id = self.blocks.len();
        self.blocks.push(CfgBasicBlock {
            id,
            label: format!("BB{} ({})", id, label),
            kind: kind.to_string(),
            stmts: Vec::new(),
            successors: Vec::new(),
            predecessors: Vec::new(),
            dominators: Vec::new(),
        });
        id
    }

    fn add_edge(&mut self, from: usize, to: usize, label: &str) {
        if !self.blocks[from].successors.iter().any(|(d, _)| *d == to) {
            self.blocks[from].successors.push((to, label.to_string()));
        }
    }

    fn lower_stmts(&mut self, stmts: &[Stmt], mut cur: usize, exit: usize) -> Option<usize> {
        for s in stmts {
            match s {
                Stmt::Comment { .. } => {}
                Stmt::Let { name, .. } => {
                    self.blocks[cur].stmts.push(format!("let {}", name));
                }
                Stmt::Assign { target, .. } => {
                    self.blocks[cur]
                        .stmts
                        .push(format!("assign {}", target.root_var()));
                }
                Stmt::Assert { .. } | Stmt::AssertEq { .. } => {
                    self.blocks[cur].stmts.push("assert(...)".to_string());
                }
                Stmt::Expr { .. } => {
                    self.blocks[cur].stmts.push("expr".to_string());
                }
                Stmt::Return { .. } => {
                    self.blocks[cur].stmts.push("return".to_string());
                    self.add_edge(cur, exit, "return");
                    return None;
                }
                Stmt::Break { .. } => {
                    self.blocks[cur].stmts.push("break".to_string());
                    if let Some(&(_, after_bb)) = self.loop_stack.last() {
                        self.add_edge(cur, after_bb, "break");
                    }
                    return None;
                }
                Stmt::Continue { .. } => {
                    self.blocks[cur].stmts.push("continue".to_string());
                    if let Some(&(hdr_bb, _)) = self.loop_stack.last() {
                        self.add_edge(cur, hdr_bb, "continue");
                    }
                    return None;
                }
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    self.blocks[cur].stmts.push("branch if".to_string());
                    let then_bb = self.new_block("Then", "branch");
                    self.add_edge(cur, then_bb, "T");
                    let t_end = self.lower_stmts(then_body, then_bb, exit);
                    let e_end = if else_body.is_empty() {
                        Some(cur)
                    } else {
                        let else_bb = self.new_block("Else", "branch");
                        self.add_edge(cur, else_bb, "F");
                        self.lower_stmts(else_body, else_bb, exit)
                    };
                    if t_end.is_none() && e_end.is_none() {
                        return None;
                    }
                    let join_bb = self.new_block("Join", "join");
                    if let Some(te) = t_end {
                        self.add_edge(te, join_bb, "");
                    }
                    if let Some(ee) = e_end {
                        let lbl = if else_body.is_empty() { "F" } else { "" };
                        self.add_edge(ee, join_bb, lbl);
                    }
                    cur = join_bb;
                }
                Stmt::Match { arms, .. } => {
                    self.blocks[cur].stmts.push("match".to_string());
                    let mut arm_ends = Vec::new();
                    for (idx, arm) in arms.iter().enumerate() {
                        let arm_bb = self.new_block(&format!("Arm{}", idx), "branch");
                        self.add_edge(cur, arm_bb, &format!("arm_{}", idx));
                        if let Some(a_end) = self.lower_stmts(&arm.body, arm_bb, exit) {
                            arm_ends.push(a_end);
                        }
                    }
                    if arm_ends.is_empty() {
                        return None;
                    }
                    let join_bb = self.new_block("MatchJoin", "join");
                    for a_end in arm_ends {
                        self.add_edge(a_end, join_bb, "");
                    }
                    cur = join_bb;
                }
                Stmt::While { body, .. }
                | Stmt::ForEach { body, .. }
                | Stmt::ForRange { body, .. } => {
                    let hdr_bb = self.new_block("LoopHeader", "loop_header");
                    let body_bb = self.new_block("LoopBody", "loop_body");
                    let after_bb = self.new_block("LoopExit", "join");
                    self.add_edge(cur, hdr_bb, "");
                    self.add_edge(hdr_bb, body_bb, "loop");
                    self.add_edge(hdr_bb, after_bb, "done");
                    self.loop_stack.push((hdr_bb, after_bb));
                    if let Some(b_end) = self.lower_stmts(body, body_bb, exit) {
                        self.add_edge(b_end, hdr_bb, "back");
                    }
                    self.loop_stack.pop();
                    cur = after_bb;
                }
            }
        }
        Some(cur)
    }
}

use std::time::Instant;

use crate::eval::{eval_module_default, eval_tests_default};
use crate::hub::{
    AssignOp, AssignTarget, BinOp, EnumDecl, Expr, Field, FnDecl, HubModule, Intrinsic, Item,
    MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl, Type, UnaryOp,
};
use crate::lens::SpokeId;
use crate::reconcile::reconcile_modules;
use crate::refactor::optimize_module;
use crate::spokes::lens_for;
use crate::typecheck::check_module;

#[derive(Debug, Clone)]
pub struct FuzzReport {
    pub seed: u64,
    pub programs_tested: usize,
    pub spoke_roundtrips: usize,
    pub assertions_passed: usize,
    pub optimizer_checks: usize,
    pub failures: Vec<String>,
    pub elapsed_ms: u128,
}

impl FuzzReport {
    pub fn ok(&self) -> bool {
        self.failures.is_empty()
    }
}

/// Deterministic zero-dependency SplitMix64 PRNG for reproducible AST synthesis.
struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn range_usize(&mut self, upper_excl: usize) -> usize {
        if upper_excl <= 1 {
            0
        } else {
            (self.next_u64() as usize) % upper_excl
        }
    }

    fn range_i64(&mut self, low: i64, high_incl: i64) -> i64 {
        if high_incl <= low {
            return low;
        }
        let span = (high_incl as i128 - low as i128 + 1) as u128;
        (low as i128 + ((self.next_u64() as u128) % span) as i128) as i64
    }

    fn coin(&mut self) -> bool {
        (self.next_u64() & 1) == 1
    }

    fn choose<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.range_usize(items.len())]
    }
}

/// Synthesize `count` random well-typed Hub AST programs and verify:
/// 1. Central Hub static typechecker passes with 0 diagnostics.
/// 2. Hub VM executes `main()` and all synthesized `Item::Test` assertions cleanly.
/// 3. `GetPut` lens law (`lens.put(&lens.get(&hub), &hub) == Ok(hub)`) + cold `put` hold across all 7 spokes.
/// 4. Central Hub optimizer preserves static types, runtime semantics, and 7-spoke `GetPut` round-tripping.
pub fn run_fuzz_suite(seed: u64, count: usize) -> FuzzReport {
    let start = Instant::now();
    let mut rng = SplitMix64::new(seed);
    let mut spoke_roundtrips = 0usize;
    let mut assertions_passed = 0usize;
    let mut optimizer_checks = 0usize;
    let mut failures = Vec::new();

    for prog_idx in 0..count {
        let raw = synth_module(&mut rng, prog_idx);
        let hub = reconcile_modules(raw, &HubModule::new(), SpokeId::Star);

        // 1. Central Hub static typecheck
        let diags = check_module(&hub);
        if !diags.is_empty() {
            failures.push(format!(
                "program #{}: generated AST failed Hub typecheck: {:?}\nStar IR:\n{}",
                prog_idx,
                diags,
                lens_for(SpokeId::Star).get(&hub)
            ));
            continue;
        }

        // 2. Hub VM execution + unit test execution
        let ev = eval_module_default(&hub);
        if !ev.ok {
            failures.push(format!(
                "program #{}: Hub VM main() failed: {:?}\nStar IR:\n{}",
                prog_idx,
                ev.error,
                lens_for(SpokeId::Star).get(&hub)
            ));
            continue;
        }

        let test_results = eval_tests_default(&hub);
        for tr in &test_results {
            if !tr.passed {
                failures.push(format!(
                    "program #{}: unit test '{}' failed: {:?}\nStar IR:\n{}",
                    prog_idx,
                    tr.name,
                    tr.error,
                    lens_for(SpokeId::Star).get(&hub)
                ));
            } else {
                assertions_passed += 1;
            }
        }

        // 3. 7-spoke GetPut + cold Put round-trip verification
        for spoke in SpokeId::ALL {
            let lens = lens_for(spoke);
            let projected = lens.get(&hub);
            spoke_roundtrips += 1;

            match lens.put(&projected, &hub) {
                Ok(lifted) => {
                    if lifted != hub {
                        failures.push(format!(
                            "program #{} [{}]: GetPut AST mismatch!\nProjected ({}):\n{}\nExpected Star:\n{}\nActual Star:\n{}",
                            prog_idx,
                            spoke.display_name(),
                            spoke.display_name(),
                            projected,
                            lens_for(SpokeId::Star).get(&hub),
                            lens_for(SpokeId::Star).get(&lifted)
                        ));
                        continue;
                    }
                }
                Err(diag) => {
                    failures.push(format!(
                        "program #{} [{}]: GetPut parse error: {}\nProjected ({}):\n{}",
                        prog_idx,
                        spoke.display_name(),
                        diag,
                        spoke.display_name(),
                        projected
                    ));
                    continue;
                }
            }

            // Cold put from empty HubModule (verifies standalone parsing without prior metadata)
            match lens.put(&projected, &HubModule::new()) {
                Ok(cold_hub) => {
                    let cold_diags = check_module(&cold_hub);
                    if !cold_diags.is_empty() {
                        failures.push(format!(
                            "program #{} [{}]: cold Put introduced typecheck errors: {:?}",
                            prog_idx,
                            spoke.display_name(),
                            cold_diags
                        ));
                    }
                    let cold_ev = eval_module_default(&cold_hub);
                    if !cold_ev.ok || cold_ev.stdout != ev.stdout {
                        failures.push(format!(
                            "program #{} [{}]: cold Put altered VM stdout ({:?} vs {:?})",
                            prog_idx,
                            spoke.display_name(),
                            cold_ev.stdout,
                            ev.stdout
                        ));
                    }
                }
                Err(diag) => {
                    failures.push(format!(
                        "program #{} [{}]: cold Put parse error: {}",
                        prog_idx,
                        spoke.display_name(),
                        diag
                    ));
                }
            }
        }

        // 4. Optimizer + E-Graph + Wasm soundness & 13-spoke GetPut on optimized AST
        let (opt_hub, _) = optimize_module(&hub);
        optimizer_checks += 1;
        let opt_diags = check_module(&opt_hub);
        if !opt_diags.is_empty() {
            failures.push(format!(
                "program #{}: optimize_module introduced typecheck errors: {:?}",
                prog_idx, opt_diags
            ));
        }
        let opt_ev = eval_module_default(&opt_hub);
        if !opt_ev.ok || opt_ev.stdout != ev.stdout {
            failures.push(format!(
                "program #{}: optimize_module changed stdout ({:?} vs {:?})",
                prog_idx, opt_ev.stdout, ev.stdout
            ));
        }
        for spoke in SpokeId::ALL {
            let lens = lens_for(spoke);
            let code = lens.get(&opt_hub);
            match lens.put(&code, &opt_hub) {
                Ok(lifted_opt) => {
                    if lifted_opt != opt_hub {
                        failures.push(format!(
                            "program #{} [{}]: optimized Hub failed GetPut equality",
                            prog_idx,
                            spoke.display_name()
                        ));
                    }
                }
                Err(e) => {
                    failures.push(format!(
                        "program #{} [{}]: optimized Hub failed GetPut parse: {}",
                        prog_idx,
                        spoke.display_name(),
                        e
                    ));
                }
            }
        }

        let eg_rep = crate::egraph::superoptimize_egraph(&hub);
        if !eg_rep.translation_validated {
            failures.push(format!(
                "program #{}: superoptimize_egraph failed translation validation",
                prog_idx
            ));
        }
        for spoke in SpokeId::ALL {
            let lens = lens_for(spoke);
            let code = lens.get(&eg_rep.optimized_hub);
            match lens.put(&code, &eg_rep.optimized_hub) {
                Ok(lifted_eg) => {
                    if lifted_eg != eg_rep.optimized_hub {
                        failures.push(format!(
                            "program #{} [{}]: egraph optimized Hub failed GetPut equality",
                            prog_idx,
                            spoke.display_name()
                        ));
                    }
                }
                Err(e) => {
                    failures.push(format!(
                        "program #{} [{}]: egraph optimized Hub failed GetPut parse: {}",
                        prog_idx,
                        spoke.display_name(),
                        e
                    ));
                }
            }
        }

        if let Err(e) = crate::wasm::compile_wasm(&hub) {
            failures.push(format!(
                "program #{}: compile_wasm failed: {}",
                prog_idx, e
            ));
        }
    }

    FuzzReport {
        seed,
        programs_tested: count,
        spoke_roundtrips,
        assertions_passed,
        optimizer_checks,
        failures,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

// ============================================================================
// Well-Typed, Guaranteed-Terminating Hub AST Synthesizer
// ============================================================================

fn synth_module(rng: &mut SplitMix64, idx: usize) -> HubModule {
    let struct_name = "RecordBox".to_string();
    let enum_name = "ModeKind".to_string();
    let variants = vec![
        "Low".to_string(),
        "Mid".to_string(),
        "High".to_string(),
    ];

    let struct_decl = StructDecl {
        id: 0,
        name: struct_name.clone(),
        fields: vec![
            Field {
                id: 0,
                name: "score".to_string(),
                ty: Type::Int,
                meta: Metadata::new(),
            },
            Field {
                id: 0,
                name: "active".to_string(),
                ty: Type::Bool,
                meta: Metadata::new(),
            },
            Field {
                id: 0,
                name: "label".to_string(),
                ty: Type::Str,
                meta: Metadata::new(),
            },
        ],
        comments: vec![format!("Synthesized record #{}", idx)],
        meta: Metadata::new(),
    };

    let enum_decl = EnumDecl {
        id: 0,
        name: enum_name.clone(),
        variants: variants.clone(),
        comments: Vec::new(),
        meta: Metadata::new(),
    };

    let classify_fn = synth_classify_fn(rng, &enum_name, &variants);
    let calc_fn = synth_calc_fn(rng, &struct_name, &enum_name, &variants);
    let text_fn = synth_text_fn(rng);
    let main_fn = synth_main_fn(rng, &struct_name);
    let unit_test = synth_unit_test(rng, idx, &struct_name);

    HubModule {
        next_id: 1,
        items: vec![
            Item::Struct(struct_decl),
            Item::Enum(enum_decl),
            Item::Function(classify_fn),
            Item::Function(calc_fn),
            Item::Function(text_fn),
            Item::Function(main_fn),
            Item::Test(unit_test),
        ],
    }
}

fn synth_classify_fn(rng: &mut SplitMix64, enum_name: &str, variants: &[String]) -> FnDecl {
    let t1 = rng.range_i64(15, 40);
    let t2 = rng.range_i64(0, 14);
    let int_vars = vec!["val_x".to_string()];
    let c_expr = synth_int_expr(rng, &int_vars, 2);

    FnDecl {
        id: 0,
        name: "classify_mode".to_string(),
        params: vec![Param {
            id: 0,
            name: "val_x".to_string(),
            ty: Type::Int,
            meta: Metadata::new(),
        }],
        ret_ty: Type::Named(enum_name.to_string()),
        body: vec![
            Stmt::Let {
                id: 0,
                name: "probe".to_string(),
                mutable: false,
                ty: Some(Type::Int),
                value: c_expr,
                meta: Metadata::new(),
            },
            Stmt::If {
                id: 0,
                cond: Expr::Binary {
                    op: BinOp::Ge,
                    left: Box::new(Expr::Var("probe".to_string())),
                    right: Box::new(Expr::Int(t1)),
                },
                then_body: vec![Stmt::Return {
                    id: 0,
                    value: Some(Expr::EnumVariant {
                        enum_name: enum_name.to_string(),
                        variant: variants[2].clone(),
                    }),
                    meta: Metadata::new(),
                }],
                else_body: vec![Stmt::If {
                    id: 0,
                    cond: Expr::Binary {
                        op: BinOp::Ge,
                        left: Box::new(Expr::Var("probe".to_string())),
                        right: Box::new(Expr::Int(t2)),
                    },
                    then_body: vec![Stmt::Return {
                        id: 0,
                        value: Some(Expr::EnumVariant {
                            enum_name: enum_name.to_string(),
                            variant: variants[1].clone(),
                        }),
                        meta: Metadata::new(),
                    }],
                    else_body: vec![Stmt::Return {
                        id: 0,
                        value: Some(Expr::EnumVariant {
                            enum_name: enum_name.to_string(),
                            variant: variants[0].clone(),
                        }),
                        meta: Metadata::new(),
                    }],
                    meta: Metadata::new(),
                }],
                meta: Metadata::new(),
            },
        ],
        comments: Vec::new(),
        meta: Metadata::new(),
    }
}

fn synth_calc_fn(
    rng: &mut SplitMix64,
    struct_name: &str,
    enum_name: &str,
    variants: &[String],
) -> FnDecl {
    let mut stmts = Vec::new();
    let init_acc = rng.range_i64(-5, 12);
    stmts.push(Stmt::Let {
        id: 0,
        name: "acc".to_string(),
        mutable: true,
        ty: Some(Type::Int),
        value: Expr::FieldAccess {
            base: Box::new(Expr::Var("rec".to_string())),
            field: "score".to_string(),
        },
        meta: Metadata::new(),
    });

    let int_vars = vec!["acc".to_string(), "bonus".to_string()];
    let bool_vars = vec![];

    // Add a random If/Else statement with nested boolean/comparison expressions
    let cond = synth_bool_expr(rng, &int_vars, &bool_vars, 2);
    let delta_then = synth_int_expr(rng, &int_vars, 2);
    let delta_else = synth_int_expr(rng, &int_vars, 2);
    stmts.push(Stmt::If {
        id: 0,
        cond,
        then_body: vec![Stmt::Assign {
            id: 0,
            target: AssignTarget::Var("acc".to_string()),
            op: if rng.coin() {
                AssignOp::AddAssign
            } else {
                AssignOp::Set
            },
            value: delta_then,
            meta: Metadata::new(),
        }],
        else_body: vec![Stmt::Assign {
            id: 0,
            target: AssignTarget::Var("acc".to_string()),
            op: AssignOp::SubAssign,
            value: delta_else,
            meta: Metadata::new(),
        }],
        meta: Metadata::new(),
    });

    // Bounded ForRange or bounded While loop
    if rng.coin() {
        let stop = rng.range_i64(1, 4);
        let mut loop_vars = int_vars.clone();
        loop_vars.push("idx".to_string());
        let step_expr = synth_int_expr(rng, &loop_vars, 1);
        stmts.push(Stmt::ForRange {
            id: 0,
            var: "idx".to_string(),
            start: Expr::Int(0),
            end: Expr::Int(stop),
            body: vec![Stmt::Assign {
                id: 0,
                target: AssignTarget::Var("acc".to_string()),
                op: AssignOp::AddAssign,
                value: step_expr,
                meta: Metadata::new(),
            }],
            meta: Metadata::new(),
        });
    } else {
        let limit = rng.range_i64(1, 3);
        stmts.push(Stmt::Let {
            id: 0,
            name: "step_i".to_string(),
            mutable: true,
            ty: Some(Type::Int),
            value: Expr::Int(0),
            meta: Metadata::new(),
        });
        stmts.push(Stmt::While {
            id: 0,
            cond: Expr::Binary {
                op: BinOp::Lt,
                left: Box::new(Expr::Var("step_i".to_string())),
                right: Box::new(Expr::Int(limit)),
            },
            body: vec![
                Stmt::Assign {
                    id: 0,
                    target: AssignTarget::Var("step_i".to_string()),
                    op: AssignOp::AddAssign,
                    value: Expr::Int(1),
                    meta: Metadata::new(),
                },
                Stmt::Assign {
                    id: 0,
                    target: AssignTarget::Var("acc".to_string()),
                    op: AssignOp::AddAssign,
                    value: Expr::Int(init_acc),
                    meta: Metadata::new(),
                },
            ],
            meta: Metadata::new(),
        });
    }

    // ForEach over list parameter `items`
    let mut each_vars = int_vars.clone();
    each_vars.push("elem".to_string());
    let each_expr = synth_int_expr(rng, &each_vars, 1);
    stmts.push(Stmt::ForEach {
        id: 0,
        var: "elem".to_string(),
        iter: Expr::Var("items".to_string()),
        body: vec![Stmt::Assign {
            id: 0,
            target: AssignTarget::Var("acc".to_string()),
            op: AssignOp::AddAssign,
            value: each_expr,
            meta: Metadata::new(),
        }],
        meta: Metadata::new(),
    });

    // Enum or Int Match dispatch
    if rng.coin() {
        stmts.push(Stmt::Let {
            id: 0,
            name: "mode".to_string(),
            mutable: false,
            ty: Some(Type::Named(enum_name.to_string())),
            value: Expr::Call {
                func: "classify_mode".to_string(),
                args: vec![Expr::Var("acc".to_string())],
            },
            meta: Metadata::new(),
        });
        let arms: Vec<MatchArm> = variants
            .iter()
            .enumerate()
            .map(|(i, v)| MatchArm {
                pat: MatchPat::EnumVariant {
                    enum_name: enum_name.to_string(),
                    variant: v.clone(),
                },
                body: vec![Stmt::Assign {
                    id: 0,
                    target: AssignTarget::Var("acc".to_string()),
                    op: AssignOp::AddAssign,
                    value: Expr::Int((i as i64) * 3 + 1),
                    meta: Metadata::new(),
                }],
            })
            .collect();
        stmts.push(Stmt::Match {
            id: 0,
            expr: Expr::Var("mode".to_string()),
            arms,
            meta: Metadata::new(),
        });
    } else {
        let c1 = rng.range_i64(0, 2);
        stmts.push(Stmt::Match {
            id: 0,
            expr: Expr::Binary {
                op: BinOp::Mod,
                left: Box::new(Expr::intrinsic(Intrinsic::Abs(Expr::Var(
                    "acc".to_string(),
                )))),
                right: Box::new(Expr::Int(3)),
            },
            arms: vec![
                MatchArm {
                    pat: MatchPat::Int(c1),
                    body: vec![Stmt::Assign {
                        id: 0,
                        target: AssignTarget::Var("acc".to_string()),
                        op: AssignOp::AddAssign,
                        value: Expr::Int(5),
                        meta: Metadata::new(),
                    }],
                },
                MatchArm {
                    pat: MatchPat::Wildcard,
                    body: vec![Stmt::Assign {
                        id: 0,
                        target: AssignTarget::Var("acc".to_string()),
                        op: AssignOp::SubAssign,
                        value: Expr::Int(2),
                        meta: Metadata::new(),
                    }],
                },
            ],
            meta: Metadata::new(),
        });
    }

    stmts.push(Stmt::Return {
        id: 0,
        value: Some(synth_int_expr(rng, &int_vars, 1)),
        meta: Metadata::new(),
    });

    FnDecl {
        id: 0,
        name: "helper_calc".to_string(),
        params: vec![
            Param {
                id: 0,
                name: "rec".to_string(),
                ty: Type::Named(struct_name.to_string()),
                meta: Metadata::new(),
            },
            Param {
                id: 0,
                name: "items".to_string(),
                ty: Type::List(Box::new(Type::Int)),
                meta: Metadata::new(),
            },
            Param {
                id: 0,
                name: "bonus".to_string(),
                ty: Type::Int,
                meta: Metadata::new(),
            },
        ],
        ret_ty: Type::Int,
        body: stmts,
        comments: Vec::new(),
        meta: Metadata::new(),
    }
}

fn synth_text_fn(rng: &mut SplitMix64) -> FnDecl {
    let words = ["Alpha", "Beta", "Star", "Swift", "Rust"];
    let needle = rng.choose(&["a", "st", "be", "sw"]).to_string();
    let tag_word = (*rng.choose(&words)).to_string();
    let use_upper = rng.coin();

    let norm_expr = if use_upper {
        Expr::intrinsic(Intrinsic::Lower(Expr::intrinsic(Intrinsic::Upper(
            Expr::Var("raw_tag".to_string()),
        ))))
    } else {
        Expr::intrinsic(Intrinsic::Lower(Expr::Var("raw_tag".to_string())))
    };

    FnDecl {
        id: 0,
        name: "format_badge".to_string(),
        params: vec![
            Param {
                id: 0,
                name: "raw_tag".to_string(),
                ty: Type::Str,
                meta: Metadata::new(),
            },
            Param {
                id: 0,
                name: "num".to_string(),
                ty: Type::Int,
                meta: Metadata::new(),
            },
        ],
        ret_ty: Type::Str,
        body: vec![
            Stmt::Let {
                id: 0,
                name: "clean".to_string(),
                mutable: false,
                ty: Some(Type::Str),
                value: norm_expr,
                meta: Metadata::new(),
            },
            Stmt::If {
                id: 0,
                cond: Expr::intrinsic(Intrinsic::Contains {
                    haystack: Expr::Var("clean".to_string()),
                    needle: Expr::Str(needle),
                }),
                then_body: vec![Stmt::Return {
                    id: 0,
                    value: Some(Expr::Binary {
                        op: BinOp::Add,
                        left: Box::new(Expr::Binary {
                            op: BinOp::Add,
                            left: Box::new(Expr::Var("clean".to_string())),
                            right: Box::new(Expr::Str(":".to_string())),
                        }),
                        right: Box::new(Expr::intrinsic(Intrinsic::ToStr(Expr::Var(
                            "num".to_string(),
                        )))),
                    }),
                    meta: Metadata::new(),
                }],
                else_body: vec![Stmt::Return {
                    id: 0,
                    value: Some(Expr::Binary {
                        op: BinOp::Add,
                        left: Box::new(Expr::Str(format!("{}_", tag_word.to_lowercase()))),
                        right: Box::new(Expr::intrinsic(Intrinsic::ToStr(Expr::intrinsic(
                            Intrinsic::Len(Expr::Var("clean".to_string())),
                        )))),
                    }),
                    meta: Metadata::new(),
                }],
                meta: Metadata::new(),
            },
        ],
        comments: Vec::new(),
        meta: Metadata::new(),
    }
}

fn synth_main_fn(rng: &mut SplitMix64, struct_name: &str) -> FnDecl {
    let s0 = rng.range_i64(-10, 25);
    let b0 = rng.range_i64(1, 15);
    let n1 = rng.range_i64(1, 9);
    let n2 = rng.range_i64(-4, 8);
    let word = (*rng.choose(&["StarHub", "Polyglot", "SwiftSix", "LensAST"])).to_string();

    FnDecl {
        id: 0,
        name: "main".to_string(),
        params: Vec::new(),
        ret_ty: Type::Void,
        body: vec![
            Stmt::Let {
                id: 0,
                name: "nums".to_string(),
                mutable: true,
                ty: Some(Type::List(Box::new(Type::Int))),
                value: Expr::List(vec![Expr::Int(n1)]),
                meta: Metadata::new(),
            },
            Stmt::Expr {
                id: 0,
                expr: Expr::intrinsic(Intrinsic::Push {
                    list: Expr::Var("nums".to_string()),
                    value: Expr::Int(n2),
                }),
                meta: Metadata::new(),
            },
            Stmt::Let {
                id: 0,
                name: "box_val".to_string(),
                mutable: false,
                ty: Some(Type::Named(struct_name.to_string())),
                value: Expr::StructInit {
                    name: struct_name.to_string(),
                    fields: vec![
                        ("score".to_string(), Expr::Int(s0)),
                        ("active".to_string(), Expr::Bool(true)),
                        ("label".to_string(), Expr::Str(word.clone())),
                    ],
                },
                meta: Metadata::new(),
            },
            Stmt::Let {
                id: 0,
                name: "result".to_string(),
                mutable: false,
                ty: Some(Type::Int),
                value: Expr::Call {
                    func: "helper_calc".to_string(),
                    args: vec![
                        Expr::Var("box_val".to_string()),
                        Expr::Var("nums".to_string()),
                        Expr::Int(b0),
                    ],
                },
                meta: Metadata::new(),
            },
            Stmt::Let {
                id: 0,
                name: "badge".to_string(),
                mutable: false,
                ty: Some(Type::Str),
                value: Expr::Call {
                    func: "format_badge".to_string(),
                    args: vec![Expr::Str(word), Expr::Var("result".to_string())],
                },
                meta: Metadata::new(),
            },
            Stmt::Expr {
                id: 0,
                expr: Expr::intrinsic(Intrinsic::Print(vec![
                    Expr::Var("badge".to_string()),
                    Expr::Var("result".to_string()),
                ])),
                meta: Metadata::new(),
            },
        ],
        comments: Vec::new(),
        meta: Metadata::new(),
    }
}

fn synth_unit_test(rng: &mut SplitMix64, idx: usize, struct_name: &str) -> TestDecl {
    let sc = rng.range_i64(0, 20);
    let bn = rng.range_i64(1, 10);
    let probe_in = rng.range_i64(5, 80);

    TestDecl {
        id: 0,
        name: format!("generated_invariants_{}", idx),
        comments: vec!["Property-synthesized cross-language invariants".to_string()],
        body: vec![
            Stmt::Let {
                id: 0,
                name: "sample_box".to_string(),
                mutable: false,
                ty: Some(Type::Named(struct_name.to_string())),
                value: Expr::StructInit {
                    name: struct_name.to_string(),
                    fields: vec![
                        ("score".to_string(), Expr::Int(sc)),
                        ("active".to_string(), Expr::Bool(true)),
                        ("label".to_string(), Expr::Str("probe".to_string())),
                    ],
                },
                meta: Metadata::new(),
            },
            Stmt::Let {
                id: 0,
                name: "xs".to_string(),
                mutable: false,
                ty: Some(Type::List(Box::new(Type::Int))),
                value: Expr::List(vec![Expr::Int(2), Expr::Int(4)]),
                meta: Metadata::new(),
            },
            Stmt::Let {
                id: 0,
                name: "r1".to_string(),
                mutable: false,
                ty: Some(Type::Int),
                value: Expr::Call {
                    func: "helper_calc".to_string(),
                    args: vec![
                        Expr::Var("sample_box".to_string()),
                        Expr::Var("xs".to_string()),
                        Expr::Int(bn),
                    ],
                },
                meta: Metadata::new(),
            },
            // Deterministic purity check: helper_calc(sample_box, xs, bn) == r1
            Stmt::AssertEq {
                id: 0,
                left: Expr::Var("r1".to_string()),
                right: Expr::Call {
                    func: "helper_calc".to_string(),
                    args: vec![
                        Expr::Var("sample_box".to_string()),
                        Expr::Var("xs".to_string()),
                        Expr::Int(bn),
                    ],
                },
                meta: Metadata::new(),
            },
            // Non-negativity invariant: abs(r1) >= 0
            Stmt::Assert {
                id: 0,
                cond: Expr::Binary {
                    op: BinOp::Ge,
                    left: Box::new(Expr::intrinsic(Intrinsic::Abs(Expr::Var(
                        "r1".to_string(),
                    )))),
                    right: Box::new(Expr::Int(0)),
                },
                meta: Metadata::new(),
            },
            // Enum classification determinism invariant
            Stmt::AssertEq {
                id: 0,
                left: Expr::Call {
                    func: "classify_mode".to_string(),
                    args: vec![Expr::Int(probe_in)],
                },
                right: Expr::Call {
                    func: "classify_mode".to_string(),
                    args: vec![Expr::Int(probe_in)],
                },
                meta: Metadata::new(),
            },
        ],
        meta: Metadata::new(),
    }
}

fn synth_int_expr(rng: &mut SplitMix64, int_vars: &[String], depth: usize) -> Expr {
    if depth == 0 || rng.range_usize(4) == 0 {
        if !int_vars.is_empty() && rng.coin() {
            return Expr::Var(rng.choose(int_vars).clone());
        }
        return Expr::Int(rng.range_i64(-12, 18));
    }

    match rng.range_usize(7) {
        0 => {
            let op = *rng.choose(&[BinOp::Add, BinOp::Sub, BinOp::Mul]);
            Expr::Binary {
                op,
                left: Box::new(synth_int_expr(rng, int_vars, depth - 1)),
                right: Box::new(synth_int_expr(rng, int_vars, depth - 1)),
            }
        }
        1 => {
            // Safe integer division / modulo with positive non-zero literal divisor
            let op = if rng.coin() { BinOp::Div } else { BinOp::Mod };
            let div = rng.range_i64(2, 6);
            Expr::Binary {
                op,
                left: Box::new(Expr::intrinsic(Intrinsic::Abs(synth_int_expr(
                    rng,
                    int_vars,
                    depth - 1,
                )))),
                right: Box::new(Expr::Int(div)),
            }
        }
        2 => Expr::Unary {
            op: UnaryOp::Neg,
            expr: Box::new(synth_int_expr(rng, int_vars, depth - 1)),
        },
        3 => Expr::intrinsic(Intrinsic::Min(
            synth_int_expr(rng, int_vars, depth - 1),
            synth_int_expr(rng, int_vars, depth - 1),
        )),
        4 => Expr::intrinsic(Intrinsic::Max(
            synth_int_expr(rng, int_vars, depth - 1),
            synth_int_expr(rng, int_vars, depth - 1),
        )),
        5 => Expr::intrinsic(Intrinsic::Abs(synth_int_expr(rng, int_vars, depth - 1))),
        _ => {
            // Right-associated subtraction `a - (b - c)` to stress-test `needs_parens`
            let a = synth_int_expr(rng, int_vars, 0);
            let b = synth_int_expr(rng, int_vars, 0);
            let c = synth_int_expr(rng, int_vars, 0);
            Expr::Binary {
                op: BinOp::Sub,
                left: Box::new(a),
                right: Box::new(Expr::Binary {
                    op: BinOp::Sub,
                    left: Box::new(b),
                    right: Box::new(c),
                }),
            }
        }
    }
}

fn synth_bool_expr(
    rng: &mut SplitMix64,
    int_vars: &[String],
    bool_vars: &[String],
    depth: usize,
) -> Expr {
    if depth == 0 {
        if !bool_vars.is_empty() && rng.coin() {
            return Expr::Var(rng.choose(bool_vars).clone());
        }
        let op = *rng.choose(&[
            BinOp::Eq,
            BinOp::Ne,
            BinOp::Lt,
            BinOp::Le,
            BinOp::Gt,
            BinOp::Ge,
        ]);
        return Expr::Binary {
            op,
            left: Box::new(synth_int_expr(rng, int_vars, 1)),
            right: Box::new(synth_int_expr(rng, int_vars, 1)),
        };
    }

    match rng.range_usize(4) {
        0 => Expr::Binary {
            op: if rng.coin() { BinOp::And } else { BinOp::Or },
            left: Box::new(synth_bool_expr(rng, int_vars, bool_vars, depth - 1)),
            right: Box::new(synth_bool_expr(rng, int_vars, bool_vars, depth - 1)),
        },
        1 => Expr::Unary {
            op: UnaryOp::Not,
            expr: Box::new(synth_bool_expr(rng, int_vars, bool_vars, depth - 1)),
        },
        2 => {
            // Non-associative comparison equality `(a < b) == (c >= d)` to stress-test Rust/Swift/Python parens!
            let c1 = Expr::Binary {
                op: BinOp::Lt,
                left: Box::new(synth_int_expr(rng, int_vars, 0)),
                right: Box::new(synth_int_expr(rng, int_vars, 0)),
            };
            let c2 = Expr::Binary {
                op: BinOp::Ge,
                left: Box::new(synth_int_expr(rng, int_vars, 0)),
                right: Box::new(synth_int_expr(rng, int_vars, 0)),
            };
            Expr::Binary {
                op: BinOp::Eq,
                left: Box::new(c1),
                right: Box::new(c2),
            }
        }
        _ => synth_bool_expr(rng, int_vars, bool_vars, 0),
    }
}

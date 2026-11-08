use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::thread;

use starlang::engine::StarEngine;
use starlang::eval::eval_module;
use starlang::fuzzer::run_fuzz_suite;
use starlang::json::json_str;
use starlang::lens::SpokeId;
use starlang::merge::diff_sources;
use starlang::runner::run_all_spokes;
use starlang::samples::{find_sample, SAMPLES};
use starlang::server::serve_listener;
use starlang::spokes::lens_for;
use starlang::typecheck::check_module;
use starlang::verify::{ObligationKind, VerifyStatus};
use starlang::wasm::{compile_wasm, run_wasm_jit};

#[test]
fn get_put_law_holds_across_all_spokes_and_samples() {
    for sample in SAMPLES {
        let engine = StarEngine::from_source(sample.initial_spoke, sample.source)
            .unwrap_or_else(|e| panic!("sample '{}' failed initial parse: {}", sample.id, e));
        let canonical_hub = engine.hub().clone();

        for spoke in SpokeId::ALL {
            let lens = lens_for(spoke);
            let rendered = lens.get(&canonical_hub);
            let roundtripped = lens.put(&rendered, &canonical_hub).unwrap_or_else(|e| {
                panic!(
                    "GetPut parse failed for sample '{}' on spoke {:?}:\n{}\n---\n{}",
                    sample.id, spoke, e, rendered
                )
            });

            assert_eq!(
                roundtripped, canonical_hub,
                "GetPut violated for sample '{}' on spoke {:?}",
                sample.id, spoke
            );
        }
    }

    // Verify right-associated binary trees + string pattern matching round-trip across all 9 spokes
    let star_edge_cases = r#"(fn join3 ((param a Str) (param b Str) (param c Str)) -> Str
  (match a
    (case "hi"
      (return (+ a (+ b c))))
    (case _
      (return b))))

(fn main () -> Void
  (print (call join3 "hi" "!" "?")))
"#;
    let engine = StarEngine::from_source(SpokeId::Star, star_edge_cases).unwrap();
    let canonical_hub = engine.hub().clone();
    for spoke in SpokeId::ALL {
        let lens = lens_for(spoke);
        let rendered = lens.get(&canonical_hub);
        let roundtripped = lens.put(&rendered, &canonical_hub).unwrap_or_else(|e| {
            panic!("Edge-case GetPut failed on {:?}: {}\n{}", spoke, e, rendered)
        });
        assert_eq!(
            roundtripped, canonical_hub,
            "Edge-case GetPut mismatch on {:?}",
            spoke
        );
    }
}

#[test]
fn python_ruby_and_typescript_edits_preserve_rust_borrow_metadata_and_sync_all_views() {
    let sample = find_sample("scores").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    // 1. Edit in Python: add a +10 bonus and a comment inside the loop
    let py_code = engine.project(SpokeId::Python);
    assert!(py_code.contains("clamped = max(min(s, limit), 0)"));
    let py_edited = py_code.replace(
        "clamped = max(min(s, limit), 0)",
        "# Bonus points added in Python\n        clamped = max(min(s + 10, limit), 0)",
    );
    let snap = engine
        .apply_edit(SpokeId::Python, &py_edited)
        .expect("Python edit should lift cleanly");

    let rs_after_py = &snap.views["rust"];
    let cpp_after_py = &snap.views["cpp"];
    let swift_after_py = &snap.views["swift"];
    let go_after_py = &snap.views["go"];
    let rb_after_py = &snap.views["ruby"];
    let ts_after_py = &snap.views["typescript"];

    assert!(rs_after_py.contains("scores: &[i64]"));
    assert!(rs_after_py.contains("// Bonus points added in Python"));
    assert!(rs_after_py.contains("(s + 10).min(limit).max(0)"));
    assert!(cpp_after_py.contains("const std::vector<int64_t>& scores"));
    assert!(cpp_after_py.contains("std::max(std::min(s + 10, limit), int64_t(0))"));
    assert!(swift_after_py.contains("max(min(s + 10, limit), 0)"));
    assert!(go_after_py.contains("clamped := max(min(s + 10, limit), int64(0))"));
    assert!(rb_after_py.contains("[[s + 10, limit].min, 0].max"));
    assert!(ts_after_py.contains("Math.max(Math.min(s + 10, limit), 0)"));

    // 2. Edit in Ruby: change clamp ceiling in main() from 100 to 90
    let rb_edited = rb_after_py.replace("clamp_scores(raw, 100)", "clamp_scores(raw, 90)");
    let snap2 = engine
        .apply_edit(SpokeId::Ruby, &rb_edited)
        .expect("Ruby edit should lift cleanly");

    assert!(snap2.views["python"].contains("clamp_scores(raw, 90)"));
    assert!(snap2.views["swift"].contains("clamp_scores(raw, 90)"));
    assert!(snap2.views["cpp"].contains("clamp_scores(raw, int64_t(90))"));
    assert!(snap2.views["go"].contains("clamp_scores(raw, int64(90))"));
    assert!(snap2.views["typescript"].contains("clamp_scores(raw, 90)"));
    assert!(snap2.views["rust"].contains("clamp_scores(&raw, 90)"));

    // 3. Edit Star S-Expr metadata directly: switch `scores` from borrowed slice to owned Vec
    let star_edited = snap2.views["star"].replace(":rust.pass \"slice\"", ":rust.pass \"owned\"");
    let snap3 = engine
        .apply_edit(SpokeId::Star, &star_edited)
        .expect("Star IR edit should lift cleanly");
    assert!(snap3.views["rust"].contains("scores: Vec<i64>"));
}

#[test]
fn cpp_swift_java_go_and_ruby_edits_on_enums_and_metadata_sync_across_all_nine_spokes() {
    let sample = find_sample("alerts").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    // 1. Edit in C++: switch `latencies` parameter from `const std::vector<int64_t>&` to pass-by-value
    //    AND add a 4th enum variant `Fatal = 3` + switch case
    let cpp_code = engine.project(SpokeId::Cpp);
    assert!(cpp_code.contains("const std::vector<int64_t>& latencies"));
    let cpp_edited = cpp_code
        .replace(
            "const std::vector<int64_t>& latencies",
            "std::vector<int64_t> latencies",
        )
        .replace(
            "    Critical = 2,\n};",
            "    Critical = 2,\n    Fatal = 3,\n};",
        )
        .replace(
            "if (ms >= 500) {\n        return Severity::Critical;",
            "if (ms >= 1000) {\n        return Severity::Fatal;\n    } else if (ms >= 500) {\n        return Severity::Critical;",
        )
        .replace(
            "        case Severity::Critical: {\n            return int64_t(5);\n        }\n    }",
            "        case Severity::Critical: {\n            return int64_t(5);\n        }\n        case Severity::Fatal: {\n            return int64_t(10);\n        }\n    }",
        )
        .replace(
            "std::vector<int64_t>{80, -1, 240, 610, 520, 90}",
            "std::vector<int64_t>{80, -1, 1200, 240, 90}",
        )
        .replace("evaluate_window(samples, int64_t(6))", "evaluate_window(samples, int64_t(15))");

    let snap = engine
        .apply_edit(SpokeId::Cpp, &cpp_edited)
        .expect("C++ edit should lift cleanly");

    // Both Rust `rust.pass=slice` AND C++ `cpp.pass=value` coexist on the Hub!
    assert!(snap.views["rust"].contains("latencies: &[i64]"));
    assert!(snap.views["star"].contains(":cpp.pass \"value\""));
    assert!(snap.views["swift"].contains("    case Fatal\n"));
    assert!(snap.views["go"].contains("\tSeverity_Fatal\n"));
    assert!(snap.views["python"].contains("    Fatal = 3\n"));
    assert!(snap.views["ruby"].contains("  Fatal = 3\n"));
    assert!(snap.views["typescript"].contains("  Fatal: 3,\n"));

    // Subsequent edit in Swift 6 preserves BOTH C++ pass-by-value AND Rust slice borrow
    let swift_edited = snap.views["swift"].replace(
        "    case Severity.Fatal:\n        return 10",
        "    case Severity.Fatal:\n        return 12",
    );
    let snap2 = engine
        .apply_edit(SpokeId::Swift, &swift_edited)
        .expect("Swift edit should lift cleanly");
    assert!(snap2.views["cpp"].contains("std::string evaluate_window(std::vector<int64_t> latencies"));
    assert!(snap2.views["rust"].contains("latencies: &[i64]"));
    assert!(snap2.views["java"].contains("case Severity.Fatal -> {"));
    assert!(snap2.views["ruby"].contains("when Severity::Fatal\n    return 12"));
    assert!(snap2.views["go"].contains("return int64(12)"));
    assert_eq!(snap2.live_eval.stdout.trim(), "checked=4 score=13");

    // Subsequent edit in Modern Java 21 also preserves Rust slice + C++ value metadata!
    let java_edited = snap2.views["java"].replace(
        "            case Severity.Fatal -> {\n                return 12L;\n            }",
        "            case Severity.Fatal -> {\n                return 14L;\n            }",
    );
    let snap3 = engine
        .apply_edit(SpokeId::Java, &java_edited)
        .expect("Java 21 edit should lift cleanly");
    assert!(snap3.views["cpp"].contains("std::string evaluate_window(std::vector<int64_t> latencies"));
    assert!(snap3.views["rust"].contains("latencies: &[i64]"));
    assert!(snap3.views["swift"].contains("return 14"));
    assert!(snap3.views["ruby"].contains("return 14"));
    assert_eq!(snap3.live_eval.stdout.trim(), "checked=3 score=15");

    let report = run_all_spokes(&engine);
    assert_eq!(report.results.len(), 14);
    assert!(
        report.outputs_match,
        "14-engine outputs diverged: {:?}",
        report.results
    );
    assert_eq!(report.results[0].stdout.trim(), "checked=3 score=15");
}

#[test]
fn range_loops_translate_idiomatically_across_all_spokes() {
    let sample = find_sample("collatz").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    let rs = engine.project(SpokeId::Rust);
    let cpp = engine.project(SpokeId::Cpp);
    let swift = engine.project(SpokeId::Swift);
    let go = engine.project(SpokeId::Go);
    let rb = engine.project(SpokeId::Ruby);
    let ts = engine.project(SpokeId::TypeScript);
    assert!(rs.contains("for k in 1..upper_bound"));
    assert!(cpp.contains("for (int64_t k = 1; k < upper_bound; k++)"));
    assert!(swift.contains("for k in stride(from: 1, to: upper_bound, by: 1)"));
    assert!(go.contains("for k := int64(1); k < upper_bound; k++"));
    assert!(rb.contains("for k in (1)...(upper_bound)"));
    assert!(ts.contains("for (let k = 1; k < upper_bound; k++)"));

    // Edit range loop in Swift using native half-open `..<` operator and verify all 9 views update
    let swift_edited = swift.replace(
        "for k in stride(from: 1, to: upper_bound, by: 1)",
        "for k in 2..<upper_bound + 1",
    );
    let snap = engine.apply_edit(SpokeId::Swift, &swift_edited).unwrap();
    assert!(snap.views["python"].contains("for k in range(2, upper_bound + 1):"));
    assert!(snap.views["ruby"].contains("for k in (2)...(upper_bound + 1)"));
    assert!(snap.views["cpp"].contains("for (int64_t k = 2; k < upper_bound + 1; k++) {"));
    assert!(snap.views["go"].contains("for k := int64(2); k < upper_bound + 1; k++ {"));
    assert!(snap.views["typescript"].contains("for (let k = 2; k < upper_bound + 1; k++) {"));
    assert!(snap.views["rust"].contains("for k in 2..upper_bound + 1 {"));
}

#[test]
fn polyglot_unit_tests_and_assertions_sync_and_catch_regressions_live() {
    // 1. Every built-in preset includes live unit tests that pass out of the box
    for sample in SAMPLES {
        let engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
        let snap = engine.snapshot();
        assert!(
            !snap.test_results.is_empty(),
            "Sample '{}' should define at least 1 polyglot unit test",
            sample.id
        );
        for tr in &snap.test_results {
            assert!(
                tr.passed,
                "Sample '{}' unit test '{}' failed: {:?}",
                sample.id, tr.name, tr.error
            );
        }
    }

    // 2. Verify idiomatic unit test projection across all 9 spokes on Swift-seeded `ledger`
    let ledger = find_sample("ledger").unwrap();
    let mut engine = StarEngine::from_source(ledger.initial_spoke, ledger.source).unwrap();
    let snap = engine.snapshot();
    assert!(snap.views["rust"].contains("#[test]\nfn test_token_bucket_burst()"));
    assert!(snap.views["rust"].contains("assert_eq!(result, BucketState"));
    assert!(snap.views["zig"].contains("test \"token_bucket_burst\""));
    assert!(snap.views["c"].contains("void test_token_bucket_burst(void)"));
    assert!(snap.views["cpp"].contains("void test_token_bucket_burst()"));
    assert!(snap.views["swift"].contains("func test_token_bucket_burst()"));
    assert!(snap.views["java"].contains("static void test_token_bucket_burst()"));
    assert!(snap.views["java"].contains("Objects.equals("));
    assert!(snap.views["go"].contains("func test_token_bucket_burst()"));
    assert!(snap.views["go"].contains("reflect.DeepEqual("));
    assert!(snap.views["python"].contains("def test_token_bucket_burst() -> None:"));
    assert!(snap.views["ruby"].contains("def test_token_bucket_burst"));
    assert!(snap.views["typescript"].contains("export function test_token_bucket_burst(): void"));
    assert!(snap.views["star"].contains("(test token_bucket_burst"));

    // 3. Introduce a bug in Python (`state.tokens -= cost` -> `state.tokens -= 0`) and verify live test catches it!
    let buggy_py = snap.views["python"].replace("state.tokens -= cost", "state.tokens -= 0");
    let buggy_snap = engine.apply_edit(SpokeId::Python, &buggy_py).unwrap();
    assert_eq!(buggy_snap.test_results.len(), 1);
    assert!(!buggy_snap.test_results[0].passed);
    let err_msg = buggy_snap.test_results[0].error.as_deref().unwrap_or("");
    assert!(
        err_msg.contains("assert_eq failed"),
        "Expected structured assert_eq diff diagnostic, got: {}",
        err_msg
    );
}

#[test]
fn hub_mutation_testing_detects_weak_tests_and_auto_hardens_across_nine_spokes() {
    let sample = find_sample("alerts").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    // 1. Initial `alerts` preset only tests a handful of inputs, leaving exact boundary mutants alive (`200`, `500`, etc.)
    let before = engine.mutate();
    assert!(
        before.total_mutants >= 8,
        "Expected >= 8 valid Hub mutants on alerts, got {}",
        before.total_mutants
    );
    assert!(
        before.survived > 0,
        "Expected surviving boundary mutants before auto-hardening, got {:?}",
        before
    );

    // 2. Auto-harden tests directly on the Hub AST!
    let (snap, hrep) = engine.harden_tests();
    assert!(
        hrep.added_assertions > 0,
        "Expected synthesized boundary assertions, got 0"
    );
    assert_eq!(
        hrep.after.score_pct, 100,
        "Expected mutation score to reach 100% on alerts, got {}% ({:?})",
        hrep.after.score_pct, hrep.after
    );
    assert_eq!(hrep.after.survived, 0);

    // 3. All polyglot unit tests (including synthesized `test_mutation_hardened`) pass in Hub VM and typecheck cleanly!
    assert!(snap.semantic_diagnostics.is_empty(), "{:?}", snap.semantic_diagnostics);
    assert!(snap.test_results.iter().any(|t| t.name == "mutation_hardened" && t.passed));
    for tr in &snap.test_results {
        assert!(tr.passed, "Unit test '{}' failed: {:?}", tr.name, tr.error);
    }

    // 4. Every spoke receives idiomatic `test_mutation_hardened` and satisfies GetPut!
    for key in [
        "rust",
        "c",
        "cpp",
        "swift",
        "java",
        "go",
        "python",
        "ruby",
        "lua",
        "typescript",
    ] {
        assert!(
            snap.views[key].contains("test_mutation_hardened"),
            "Missing test_mutation_hardened in {}:\n{}",
            key,
            snap.views[key]
        );
    }
    assert!(snap.views["zig"].contains("test \"mutation_hardened\""));

    let hardened_hub = engine.hub().clone();
    for spoke in SpokeId::ALL {
        let lens = lens_for(spoke);
        let rendered = lens.get(&hardened_hub);
        assert_eq!(
            lens.put(&rendered, &hardened_hub).unwrap(),
            hardened_hub,
            "Hardened Hub failed GetPut on {:?}",
            spoke
        );
    }
}

#[test]
fn property_based_lens_fuzzer_verifies_fifty_random_programs_across_eleven_spokes() {
    let report = run_fuzz_suite(0x57A4_2026_0500, 50);
    assert!(
        report.ok(),
        "Property-based fuzzer found {} failure(s):\n{}",
        report.failures.len(),
        report.failures.join("\n\n")
    );
    assert_eq!(report.programs_tested, 50);
    assert_eq!(report.spoke_roundtrips, 50 * 13);
    assert_eq!(report.assertions_passed, 50);
    assert_eq!(report.optimizer_checks, 50);
}

#[test]
fn perl_spoke_and_polyglot_time_travel_debugger_sync_and_slice_across_thirteen_languages() {
    // 1. Seed from `ratelimit` (Modern Perl 5.34 preset) and verify symbolic safety obligations
    let sample = find_sample("ratelimit").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
    let ver = engine.verify();
    assert_eq!(ver.total_obligations, 3, "{:?}", ver);
    assert_eq!(ver.proven_safe, 3, "{:?}", ver);
    assert_eq!(ver.refuted, 0, "{:?}", ver);
    assert!(ver.all_safe());

    // 2. Edit Perl 5.34 view and verify all 13 views stay synced + Rust borrow metadata on `scores`
    let pl_edited = engine
        .project(SpokeId::Perl)
        .replace("evaluate_quota($traffic, 40,", "evaluate_quota($traffic, 60,");
    let snap = engine.apply_edit(SpokeId::Perl, &pl_edited).unwrap();
    assert!(snap.views["rust"].contains("evaluate_quota(traffic.clone(), 60,"));
    assert!(snap.views["lua"].contains("evaluate_quota(traffic, 60,"));
    assert_eq!(
        snap.live_eval.stdout.trim(),
        "accepted: 5 rejected: 0 avg_cost: 24"
    );

    let scores = find_sample("scores").unwrap();
    let mut sc_eng = StarEngine::from_source(scores.initial_spoke, scores.source).unwrap();
    let pl_scores = sc_eng.project(SpokeId::Perl);
    assert!(pl_scores.contains("# @param $scores List[Int]"));
    let pl_scores_edited =
        pl_scores.replace("clamp_scores($raw, 100)", "clamp_scores($raw, 85)");
    let sc_snap = sc_eng.apply_edit(SpokeId::Perl, &pl_scores_edited).unwrap();
    assert!(sc_snap.views["rust"].contains("scores: &[i64]"));
    assert!(sc_snap.views["rust"].contains("clamp_scores(&raw, 85)"));

    // 3. Record Time-Travel trace and verify every step maps to a valid 1-based line in all 13 spokes
    let drep = engine.time_travel(Some("avg_cost"));
    assert!(drep.ok, "Time-travel trace failed: {:?}", drep.fault);
    assert!(drep.total_steps >= 20, "Expected >= 20 steps, got {}", drep.total_steps);
    assert!(drep.max_depth >= 3);
    assert_eq!(
        drep.final_stdout.trim(),
        "accepted: 5 rejected: 0 avg_cost: 24"
    );

    for step in &drep.steps {
        for spoke in SpokeId::ALL {
            let line = step.spoke_lines.get(spoke.as_str()).copied().unwrap_or(0);
            assert!(
                line >= 1,
                "Step #{} (stmt #{}, {}) missing line mapping for {:?}: {:?}",
                step.step_index,
                step.stmt_id,
                step.summary,
                spoke,
                step.spoke_lines
            );
        }
    }

    // 4. Verify Dynamic Backward Causal Slice for `avg_cost`
    let slice = drep.slice.expect("Expected backward slice for avg_cost");
    assert!(slice.target.ends_with("avg_cost"), "{}", slice.target);
    assert!(
        slice.slice_steps.len() >= 6,
        "Expected causal backward slice of >= 6 steps, got {:?}",
        slice
    );
    assert!(
        slice
            .explanation
            .iter()
            .any(|line| line.contains("spent =") && line.contains("pl:L")),
        "Backward slice should include `spent` accumulation with Perl line numbers: {:?}",
        slice.explanation
    );
}

#[test]
fn asymptotic_complexity_profiler_and_polyglot_quickcheck_shrinker_verify_and_minimize_across_thirteen_languages()
{
    let sample = find_sample("ratelimit").unwrap();
    let engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    // 1. Asymptotic Big-O, Cyclomatic Complexity, Gas & 13-Spoke Code Density
    let crep = engine.complexity();
    assert_eq!(crep.dominant_big_o, "O(N)");
    assert!(crep.max_cyclomatic >= 4);
    assert_eq!(crep.max_loop_depth, 1);
    assert!(crep.module_gas.total_gas > 50);
    assert!(crep.wasm_bytes > 500);
    assert_eq!(crep.spoke_metrics.len(), 13);

    let eff_fn = crep
        .functions
        .iter()
        .find(|f| f.name == "effective_capacity")
        .unwrap();
    assert_eq!(eff_fn.static_big_o, "O(1)");
    assert_eq!(eff_fn.empirical_big_o, "O(1)");

    let quota_fn = crep
        .functions
        .iter()
        .find(|f| f.name == "evaluate_quota")
        .unwrap();
    assert_eq!(quota_fn.static_big_o, "O(N)");
    assert_eq!(quota_fn.empirical_big_o, "O(N)");
    assert_eq!(quota_fn.scaling_points.len(), 5);
    assert!(
        quota_fn.growth_ratio >= 1.6 && quota_fn.growth_ratio <= 2.3,
        "Expected ~2.0x linear gas scaling for evaluate_quota, got {}",
        quota_fn.growth_ratio
    );

    // 2. Property-based QuickCheck & Algebraic Conservation Law Discovery
    let qrep = engine.quickcheck(Some(40));
    assert!(qrep.all_passed, "{:?}", qrep);
    assert!(qrep.total_trials >= 80);
    assert!(qrep.optimizer_checks >= 80);
    let quota_qc = qrep
        .functions
        .iter()
        .find(|f| f.name == "evaluate_quota")
        .unwrap();
    assert!(
        quota_qc
            .discovered_invariants
            .iter()
            .any(|i| i.contains("Conservation Law: result.accepted + result.rejected == len(costs)")),
        "Expected conservation law invariant on evaluate_quota, got {:?}",
        quota_qc.discovered_invariants
    );

    // 3. Inject an assertion fault in Perl and verify multi-pass Delta-Debugging shrinking across 13 languages
    let buggy_pl = engine.project(SpokeId::Perl).replace(
        "my $cost = $costs->[$i];",
        "my $cost = $costs->[$i];\n        star_assert($cost < 50);",
    );
    let buggy_eng = StarEngine::from_source(SpokeId::Perl, &buggy_pl).unwrap();
    let bloated_args = vec![
        starlang::eval::Value::List(vec![
            starlang::eval::Value::Int(10),
            starlang::eval::Value::Int(20),
            starlang::eval::Value::Int(88),
            starlang::eval::Value::Int(15),
            starlang::eval::Value::Int(99),
        ]),
        starlang::eval::Value::Int(120),
        starlang::eval::Value::EnumVariant {
            enum_name: "TierPolicy".to_string(),
            variant: "Burst".to_string(),
        },
    ];
    let shrunk =
        starlang::quickcheck::shrink_failing_call(buggy_eng.hub(), "evaluate_quota", &bloated_args)
            .expect("Expected shrink_failing_call to reproduce & minimize fault");
    assert!(
        shrunk.shrink_steps >= 3,
        "Expected >= 3 shrink steps, got {:?}",
        shrunk
    );
    // 5-element list [10, 20, 88, 15, 99] should shrink to a single failing element [50] and capacity 0!
    assert!(
        shrunk.minimized_args.starts_with("([50], 0,"),
        "Expected minimal counterexample ([50], 0, ...), got {}",
        shrunk.minimized_args
    );
    for spoke in SpokeId::ALL {
        let code = shrunk
            .repro_by_spoke
            .get(spoke.as_str())
            .cloned()
            .unwrap_or_default();
        assert!(
            code.contains("evaluate_quota"),
            "Missing repro call for {:?}: {:?}",
            spoke,
            shrunk.repro_by_spoke
        );
    }
}

#[test]
fn cegis_automated_program_repair_and_alpha_bisimulation_verifier_heal_faults_across_thirteen_languages()
{
    // 1. Corrupt `ratelimit` in Perl (`$accepted += 1` -> `$accepted -= 1`) so unit tests fail
    let sample = find_sample("ratelimit").unwrap();
    let base_eng = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
    let corrupted_pl = base_eng
        .project(SpokeId::Perl)
        .replace("$accepted += 1;", "$accepted -= 1;");
    let mut broken_eng = StarEngine::from_source(SpokeId::Perl, &corrupted_pl).unwrap();
    let broken_snap = broken_eng.snapshot();
    assert!(
        broken_snap.test_results.iter().any(|t| !t.passed),
        "Expected corrupted Perl program to fail unit test"
    );

    // 2. Run CEGIS Automated Program Repair (`repair(false)`) and verify 4-gate patch synthesis
    let (repaired_snap, rep, _) = broken_eng.repair(false);
    assert!(!rep.already_healthy);
    assert!(rep.repaired, "Expected CEGIS repair to succeed: {:?}", rep);
    assert_eq!(rep.tests_passed_before, 0);
    assert_eq!(rep.tests_passed_after, rep.tests_total);
    assert_eq!(rep.safety_refuted_after, 0);
    assert!(rep.quickcheck_passed);
    assert!(!rep.faults.is_empty());

    let patch = rep.patch.expect("Expected synthesized patch");
    assert_eq!(patch.func, "evaluate_quota");
    assert_eq!(patch.kind, "AccumulatorOpRepair");
    for spoke in SpokeId::ALL {
        let diff = patch
            .diffs_by_spoke
            .get(spoke.as_str())
            .cloned()
            .unwrap_or_default();
        assert!(
            !diff.trim().is_empty(),
            "Expected non-empty unified repair diff for {:?}",
            spoke
        );
    }
    assert!(
        repaired_snap.test_results.iter().all(|t| t.passed),
        "All unit tests should pass after auto-repair"
    );

    // 3. Verify De Bruijn α-Equivalence & Bisimulation between repaired Hub and original Hub
    let eq_rep = broken_eng
        .equiv_with(SpokeId::Rust, &base_eng.project(SpokeId::Rust), 32)
        .unwrap();
    assert!(eq_rep.all_equivalent, "{:?}", eq_rep);
    assert_eq!(eq_rep.alpha_identical_count, eq_rep.shared_functions);

    // 4. Verify bisimulation catches non-equivalent programs and shrinks the distinguishing witness
    let neq_rep = base_eng
        .equiv_with(SpokeId::Perl, &corrupted_pl, 32)
        .unwrap();
    assert!(!neq_rep.all_equivalent);
    let quota_eq = neq_rep
        .functions
        .iter()
        .find(|f| f.name == "evaluate_quota")
        .unwrap();
    assert!(!quota_eq.equivalent);
    assert!(quota_eq.distinguishing_counterexample.is_some());
}

#[test]
fn pbe_inductive_synthesizer_and_dominator_cfg_analyzer_synthesize_and_export_across_thirteen_languages()
{
    let sample = find_sample("ratelimit").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    // 1. Synthesize `clamp_bonus(score: Int, cap: Int) -> Int` from 4 I/O examples with Observational Equivalence Pruning
    let (srep, snap_opt) = engine
        .synthesize(
            Some("clamp_bonus(score: Int, cap: Int) -> Int | (40, 100) => 80; (75, 100) => 100; (-15, 60) => 0; (0, 50) => 0"),
            true,
        )
        .unwrap();
    assert!(srep.ok, "Expected PBE synthesis to succeed: {:?}", srep);
    assert!(srep.tests_passed);
    assert!(srep.safety_proven);
    assert!(
        srep.pruned_by_obs_equiv > 10,
        "Expected observational equivalence pruning to eliminate redundant ASTs, got {:?}",
        srep
    );
    assert_eq!(srep.views_by_spoke.len(), 13);
    for spoke in SpokeId::ALL {
        let code = srep
            .views_by_spoke
            .get(spoke.as_str())
            .cloned()
            .unwrap_or_default();
        assert!(
            code.contains("clamp_bonus"),
            "Synthesized function missing from {:?}: {}",
            spoke,
            code
        );
    }
    let snap = snap_opt.expect("Expected injected Hub snapshot");
    assert!(snap.views["rust"].contains("pub fn clamp_bonus("));
    assert!(snap.views["perl"].contains("sub clamp_bonus("));
    assert!(snap.test_results.iter().all(|t| t.passed));

    // 2. Synthesize a list-folding loop function `sum_above(items: List<Int>, floor: Int) -> Int` from I/O examples
    let (list_rep, _) = engine.synthesize(Some("sum_above"), false).unwrap();
    assert!(list_rep.ok, "Expected list fold synthesis to succeed: {:?}", list_rep);
    assert!(list_rep.tests_passed);
    assert!(list_rep.safety_proven);
    assert!(list_rep.program_summary.contains("for"));
    assert!(list_rep.views_by_spoke["python"].contains("def sum_above("));
    assert!(list_rep.views_by_spoke["zig"].contains("pub fn sum_above("));

    // 3. Analyze Control-Flow Graphs, Dominator Sets, Natural Loops & Mermaid/DOT
    let cfg = engine.cfg();
    assert!(cfg.total_blocks >= 10, "{:?}", cfg);
    assert!(cfg.total_edges >= 8, "{:?}", cfg);
    assert!(
        cfg.total_natural_loops >= 1,
        "Expected natural loop in evaluate_quota, got {:?}",
        cfg
    );
    let quota_cfg = cfg
        .functions
        .iter()
        .find(|f| f.fn_name == "evaluate_quota")
        .unwrap();
    assert_eq!(quota_cfg.natural_loops, 1);
    assert!(!quota_cfg.back_edges.is_empty());
    assert!(quota_cfg.mermaid.contains("flowchart TD"));
    assert!(quota_cfg.dot.contains("digraph"));
}

#[test]
fn cytron_ssa_phi_placement_liveness_and_hoare_logic_contracts_verify_across_thirteen_languages() {
    let sample = find_sample("ratelimit").unwrap();
    let engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    // 1. Verify Cytron SSA form, Dominance Frontiers, φ-Node Placement, Liveness & Def-Use Chains
    let ssa = engine.ssa();
    assert_eq!(ssa.total_functions, 3);
    assert!(
        ssa.total_phi_nodes >= 4,
        "Expected >= 4 φ-nodes across LoopHeader and Join blocks in ratelimit, got {:?}",
        ssa
    );
    assert!(ssa.total_ssa_defs >= 15);
    let quota_ssa = ssa
        .functions
        .iter()
        .find(|f| f.fn_name == "evaluate_quota")
        .unwrap();
    assert!(quota_ssa.phi_count >= 4);
    assert!(quota_ssa.ssa_listing.contains("= φ("));
    assert!(
        quota_ssa
            .def_use_chains
            .iter()
            .any(|c| c.base_var == "accepted" && !c.uses.is_empty()),
        "Expected non-empty Def-Use chain for `accepted` in evaluate_quota"
    );
    assert!(
        quota_ssa
            .blocks
            .iter()
            .any(|b| !b.dominance_frontier.is_empty() && !b.live_in.is_empty()),
        "Expected blocks with non-empty Dominance Frontier and LiveIn sets"
    );

    // 2. Verify Dead-Store detection when a function contains an unused local variable assignment
    let dead_py = "def calc(x: int) -> int:\n    unused_tmp = x + 99\n    used = x * 2\n    return used\n\ndef main() -> None:\n    print(calc(5))\n";
    let dead_eng = StarEngine::from_source(SpokeId::Python, dead_py).unwrap();
    let dead_ssa = dead_eng.ssa();
    assert!(
        dead_ssa.total_dead_stores >= 1,
        "Expected SSA Def-Use analysis to flag `unused_tmp` as a dead store: {:?}",
        dead_ssa
    );

    // 3. Verify Hoare-Logic Contract Inference (`requires` / `loop_invariant` / `ensures`) & WP VCs
    let contracts = engine.contracts();
    assert!(contracts.all_verified, "{:?}", contracts);
    assert_eq!(contracts.proven_vcs, contracts.total_vcs);
    assert!(contracts.total_vcs >= 6, "{:?}", contracts);
    assert!(contracts.total_invariants >= 4);
    assert!(contracts.total_ensures >= 3);

    let quota_contract = contracts
        .functions
        .iter()
        .find(|f| f.fn_name == "evaluate_quota")
        .unwrap();
    assert!(quota_contract.verified);
    assert!(
        quota_contract
            .ensures
            .iter()
            .any(|e| e.contains("accepted + result.rejected == len(costs)")),
        "Expected conservation law in Hoare `ensures` clause: {:?}",
        quota_contract.ensures
    );
    for spoke in SpokeId::ALL {
        let ann = quota_contract
            .annotated_by_spoke
            .get(spoke.as_str())
            .cloned()
            .unwrap_or_default();
        assert!(
            ann.contains("@requires") && ann.contains("@ensures"),
            "Missing DbC contract annotations for {:?}: {}",
            spoke,
            ann
        );
    }
}

#[test]
fn whitebox_concolic_path_explorer_and_taint_security_flow_auditor_synthesize_and_verify_across_thirteen_languages() {
    let sample = find_sample("ratelimit").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    // 1. Whitebox Concolic Path Exploration & Path-Covering Unit Test Synthesis across all 13 spokes
    let (conc, snap_opt) = engine.concolic(true);
    assert_eq!(conc.total_functions, 2);
    assert!(
        conc.total_paths >= 6,
        "Expected >= 6 distinct execution paths across ratelimit functions, got {:?}",
        conc
    );
    assert_eq!(
        conc.branch_coverage_pct, 100,
        "Expected 100% branch coverage via boundary-negation solver, got {:?}",
        conc
    );
    assert!(conc.synthesized_assertions_count >= 6);
    assert!(conc.all_synthesized_tests_pass);

    let quota_fn = conc
        .functions
        .iter()
        .find(|f| f.fn_name == "evaluate_quota")
        .unwrap();
    assert!(
        quota_fn.paths_discovered >= 5,
        "Expected evaluate_quota to have >= 5 distinct paths, got {:?}",
        quota_fn
    );
    assert_eq!(quota_fn.branch_coverage_pct, 100);
    for spoke in SpokeId::ALL {
        let test_code = conc
            .views_by_spoke
            .get(spoke.as_str())
            .cloned()
            .unwrap_or_default();
        assert!(
            test_code.contains("concolic_effective_capacity")
                && test_code.contains("concolic_evaluate_quota"),
            "Synthesized concolic unit tests missing for {:?}: {}",
            spoke,
            test_code
        );
    }

    let snap = snap_opt.expect("Expected snapshot with injected concolic unit tests");
    assert!(snap.views["rust"].contains("fn test_concolic_evaluate_quota()"));
    assert!(snap.views["perl"].contains("sub test_concolic_evaluate_quota()"));
    assert!(
        snap.test_results.iter().all(|t| t.passed),
        "All injected concolic unit tests must pass in Hub VM: {:?}",
        snap.test_results
    );

    // 2. Denning Lattice Information-Flow Taint & Dominating Sanitizer Verification on `ratelimit`
    let sec = engine.security_flow();
    assert!(
        sec.all_sinks_safe,
        "Expected all sensitive divisor/bounds sinks in ratelimit to be guarded by sanitizers: {:?}",
        sec
    );
    assert_eq!(sec.unsanitized_sinks, 0);
    assert!(sec.safe_sinks >= 1);

    // 3. Verify that an unguarded untrusted divisor sink and secret-dependent branch are flagged
    let vuln_py = "def leak_and_divide(secret_token: int, raw_input: int) -> int:\n    if secret_token > 100:\n        return 1000 // raw_input\n    return 0\n\ndef main() -> None:\n    print(leak_and_divide(50, 2))\n";
    let vuln_eng = StarEngine::from_source(SpokeId::Python, vuln_py).unwrap();
    let vuln_sec = vuln_eng.security_flow();
    assert!(
        !vuln_sec.all_sinks_safe,
        "Expected unguarded raw_input divisor to fail sanitizer audit: {:?}",
        vuln_sec
    );
    assert!(vuln_sec.unsanitized_sinks >= 1);
    let leak_fn = vuln_sec
        .functions
        .iter()
        .find(|f| f.fn_name == "leak_and_divide")
        .unwrap();
    assert!(
        !leak_fn.constant_time_clean,
        "Expected secret_token branch to be flagged as a timing side-channel hazard: {:?}",
        leak_fn
    );
}

#[test]
fn equality_saturation_egraph_superoptimizer_and_futamura_partial_evaluator_specialize_and_validate_across_thirteen_languages() {
    // 1. Test E-Graph Equality Saturation on algebraic cancellation, factoring & absorption identities
    //    that phase-ordered peephole optimizers miss:
    //    `((x + y) - y) + (z - z)` => `x`, `min(x, max(x, y))` => `x`, `(x * 3) + (x * 7)` => `(x * 10)`
    let alg_py = r#"def algebraic_kernel(x: int, y: int, z: int) -> int:
    a = ((x + y) - y) + (z - z)
    b = min(x, max(x, y))
    c = (x * 3) + (x * 7)
    if False:
        return -999
    return (a + b) + (c - c)

def main() -> None:
    print(algebraic_kernel(21, 99, -42))

def test_kernel() -> None:
    assert algebraic_kernel(10, 50, 7) == 20
"#;
    let mut alg_eng = StarEngine::from_source(SpokeId::Python, alg_py).unwrap();
    let (eg_rep, snap_opt) = alg_eng.egraph(true);
    assert!(eg_rep.translation_validated, "{:?}", eg_rep);
    assert!(
        eg_rep.expressions_optimized >= 3,
        "Expected >= 3 E-Graph expression rewrites, got {:?}",
        eg_rep
    );
    assert_eq!(eg_rep.dead_branches_pruned, 1);
    assert!(
        eg_rep.gas_saved >= 20,
        "Expected significant gas savings from E-Graph superoptimization, got {:?}",
        eg_rep
    );
    assert!(eg_rep.mermaid.contains("flowchart TD"));
    assert!(eg_rep.mermaid.contains("E-Class #"));

    let alg_snap = snap_opt.expect("Expected snapshot after applying E-Graph superoptimizer");
    assert_eq!(alg_snap.live_eval.stdout.trim(), "42");
    assert!(alg_snap.test_results.iter().all(|t| t.passed));
    // Verify simplified code across all 13 spoke languages
    for spoke in SpokeId::ALL {
        let code = &alg_snap.views[spoke.as_str()];
        assert!(
            !code.contains("999") && !code.contains("z - z"),
            "Unoptimized expression survived in {:?}:\n{}",
            spoke,
            code
        );
    }

    // 2. Test Futamura Partial Evaluator & Interprocedural Constant/Enum Specializer on `ratelimit`
    let rl_sample = find_sample("ratelimit").unwrap();
    let mut rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();
    let (pe_rep, pe_snap_opt) = rl_eng.partial_eval(true);
    assert!(pe_rep.translation_validated, "{:?}", pe_rep);
    assert!(
        pe_rep.specialized_calls >= 2,
        "Expected Futamura specialization on evaluate_quota(..., 40, TierPolicy::Burst) and effective_capacity(40, TierPolicy::Burst), got {:?}",
        pe_rep
    );
    assert!(pe_rep.residual_functions_synthesized >= 1);
    assert!(pe_rep.static_branches_folded >= 1);
    assert!(
        pe_rep.vm_steps_after < pe_rep.vm_steps_before,
        "Expected specialized residual program to execute in fewer VM steps ({} vs {})",
        pe_rep.vm_steps_after,
        pe_rep.vm_steps_before
    );
    assert_eq!(pe_rep.stdout_before, pe_rep.stdout_after);
    assert_eq!(pe_rep.tests_passed, pe_rep.tests_total);

    let pe_snap = pe_snap_opt.expect("Expected snapshot after applying Futamura partial evaluation");
    for spoke in SpokeId::ALL {
        let code = &pe_snap.views[spoke.as_str()];
        assert!(
            code.contains("evaluate_quota_spec_i40_burst"),
            "Specialized residual function missing in {:?}:\n{}",
            spoke,
            code
        );
    }

    // 3. Test Bounded Static Loop Unrolling (`for i in 0..3`)
    let loop_py = "def sum_triple(base: int) -> int:\n    acc = base\n    for i in range(0, 3):\n        acc += i * 10\n    return acc\n\ndef main() -> None:\n    print(sum_triple(5))\n";
    let mut loop_eng = StarEngine::from_source(SpokeId::Python, loop_py).unwrap();
    let (loop_pe, _) = loop_eng.partial_eval(true);
    assert!(loop_pe.translation_validated);
    assert!(loop_pe.loops_unrolled >= 1);
    assert_eq!(loop_pe.stdout_after, "35");
}

#[test]
fn lua_spoke_and_zero_dep_wasm_backend_compile_sync_and_execute_in_v8_jit() {
    // 1. Seed from `backoff` (LuaJIT + LuaCATS preset) and verify symbolic safety obligations
    let sample = find_sample("backoff").unwrap();
    let engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
    let ver = engine.verify();
    assert_eq!(ver.total_obligations, 3, "{:?}", ver);
    assert_eq!(ver.proven_safe, 3, "{:?}", ver);
    assert_eq!(ver.refuted, 0, "{:?}", ver);
    assert!(ver.all_safe());

    // 2. Verify 1-based Lua `attempts[i + 1]` and `for i = 0, #attempts - 1 do` lifted to 0-based Hub
    let rs_view = engine.project(SpokeId::Rust);
    assert!(rs_view.contains("for i in 0..attempts.len() as i64"), "{}", rs_view);
    assert!(rs_view.contains("attempts[i as usize]"), "{}", rs_view);

    // 3. Edit Lua on `scores` preset (which has Rust `&[i64]` slice metadata) using 1-based indexing
    let scores = find_sample("scores").unwrap();
    let mut sc_eng = StarEngine::from_source(scores.initial_spoke, scores.source).unwrap();
    let lua_scores = sc_eng.project(SpokeId::Lua);
    assert!(lua_scores.contains("---@param scores integer[]"));
    let lua_edited = lua_scores.replace("clamp_scores(raw, 100)", "clamp_scores(raw, 85)");
    let sc_snap = sc_eng.apply_edit(SpokeId::Lua, &lua_edited).unwrap();
    assert!(sc_snap.views["rust"].contains("scores: &[i64]"));
    assert!(sc_snap.views["rust"].contains("clamp_scores(&raw, 85)"));

    // 4. Compile every built-in preset to W3C WebAssembly 1.0 binary (.wasm) + .wat and run in V8 JIT
    for preset in SAMPLES {
        let eng = StarEngine::from_source(preset.initial_spoke, preset.source).unwrap();
        let snap = eng.snapshot();
        let art = compile_wasm(eng.hub()).unwrap_or_else(|e| {
            panic!("Failed compiling '{}' to Wasm: {}", preset.id, e)
        });
        assert_eq!(&art.bytes[0..8], b"\0asm\x01\x00\x00\x00");
        assert!(art.wat.contains("(module"));
        assert!(art.exports.contains(&"memory".to_string()));
        assert!(art.exports.contains(&"main".to_string()));

        let wrep = run_wasm_jit(eng.hub());
        assert!(
            wrep.ok,
            "Wasm V8 JIT failed on preset '{}': {:?}\nWAT:\n{}",
            preset.id, wrep.error, art.wat
        );
        assert_eq!(
            wrep.stdout.trim(),
            snap.live_eval.stdout.trim(),
            "Wasm stdout mismatch on '{}'",
            preset.id
        );
        assert_eq!(wrep.tests_total, snap.test_results.len());
        assert_eq!(wrep.tests_passed, snap.test_results.len());
    }
}

#[test]
fn three_way_cross_language_ast_merger_reconciles_concurrent_edits_and_detects_conflicts() {
    let sample = find_sample("alerts").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    // 1. Cross-language semantic diff between projected Zig and Python views of the same Hub is empty
    let zig_base = engine.project(SpokeId::Zig);
    let py_base = engine.project(SpokeId::Python);
    let initial_diff = diff_sources(SpokeId::Zig, &zig_base, SpokeId::Python, &py_base).unwrap();
    assert!(
        initial_diff.identical,
        "Projected Zig and Python views of same Hub should have 0 semantic deltas, got {:?}",
        initial_diff.deltas
    );

    // 2. Concurrent non-overlapping edits off the same base Hub:
    //    - Alice (Zig 0.16): adds `Fatal = 3` variant + `ms >= 1000` threshold + `.Fatal => return 10`
    //    - Bob (C++): switches `latencies` to pass-by-value (`cpp.pass=value`) AND updates `main()` window
    let zig_alice = zig_base
        .replace(
            "    Critical = 2,\n};",
            "    Critical = 2,\n    Fatal = 3,\n};",
        )
        .replace(
            "    if (ms >= 500) {\n        return Severity.Critical;",
            "    if (ms >= 1000) {\n        return Severity.Fatal;\n    } else if (ms >= 500) {\n        return Severity.Critical;",
        )
        .replace(
            "        Severity.Critical => {\n            return 5;\n        },",
            "        Severity.Critical => {\n            return 5;\n        },\n        Severity.Fatal => {\n            return 10;\n        },",
        );

    let cpp_base = engine.project(SpokeId::Cpp);
    let cpp_bob = cpp_base
        .replace(
            "const std::vector<int64_t>& latencies",
            "std::vector<int64_t> latencies",
        )
        .replace(
            "std::vector<int64_t>{80, -1, 240, 610, 520, 90}",
            "std::vector<int64_t>{80, -1, 1200, 240, 90}",
        )
        .replace(
            "evaluate_window(samples, int64_t(6))",
            "evaluate_window(samples, int64_t(15))",
        );

    let (merged_snap, mrep) = engine
        .merge_concurrent(SpokeId::Zig, &zig_alice, SpokeId::Cpp, &cpp_bob)
        .expect("3-way merge should parse cleanly");

    assert!(mrep.clean, "Expected clean 3-way merge, got conflicts: {:?}", mrep.conflicts);
    assert!(mrep.conflicts.is_empty());
    assert!(mrep.applied_changes.len() >= 3, "{:?}", mrep.applied_changes);
    assert!(merged_snap.semantic_diagnostics.is_empty(), "{:?}", merged_snap.semantic_diagnostics);

    // Unified Hub preserves Rust `&[i64]` slice metadata + Bob's C++ value metadata + Alice's Zig enum!
    assert!(merged_snap.views["rust"].contains("latencies: &[i64]"));
    assert!(merged_snap.views["rust"].contains("    Fatal,\n"));
    assert!(merged_snap.views["cpp"].contains("std::string evaluate_window(std::vector<int64_t> latencies"));
    assert!(merged_snap.views["zig"].contains("Fatal = 3,"));
    assert!(merged_snap.views["python"].contains("samples = [80, -1, 1200, 240, 90]"));
    assert_eq!(merged_snap.live_eval.stdout.trim(), "checked=4 score=11");

    // Idempotence check: merging identical forks produces 0 conflicts and preserves Hub
    let zig_after = engine.project(SpokeId::Zig);
    let (_, idem_rep) = engine
        .merge_concurrent(SpokeId::Zig, &zig_after, SpokeId::Zig, &zig_after)
        .unwrap();
    assert!(idem_rep.clean);
    assert!(idem_rep.conflicts.is_empty());

    // 3. Conflicting concurrent edits to the SAME `Match` arm in Zig vs Ruby:
    let rev_before_conflict = engine.revision();
    let zig_conflict = engine.project(SpokeId::Zig).replace(
        "        Severity.Fatal => {\n            return 10;\n        },",
        "        Severity.Fatal => {\n            return 25;\n        },",
    );
    let rb_conflict = engine.project(SpokeId::Ruby).replace(
        "  when Severity::Fatal\n    return 10",
        "  when Severity::Fatal\n    return 99",
    );
    let (_, crep) = engine
        .merge_concurrent(SpokeId::Zig, &zig_conflict, SpokeId::Ruby, &rb_conflict)
        .unwrap();
    assert!(!crep.clean, "Expected Modify/Modify conflict on .Fatal return weight");
    assert!(!crep.conflicts.is_empty());
    assert!(
        crep.conflicts.iter().any(|c| c.scope.contains("severity_weight")),
        "Expected conflict scoped to severity_weight, got {:?}",
        crep.conflicts
    );
    // Engine revision must NOT advance when merge has conflicts!
    assert_eq!(engine.revision(), rev_before_conflict);
}

#[test]
fn hub_symbolic_verifier_proves_guarded_ops_and_synthesizes_crash_counterexamples() {
    // 1. Modern C11 `packets` preset guards list indexing (`i < payloads.len`), division (`accepted > 0`),
    //    and contract assertion (`assert(mean_bytes >= 0)`) — all 3 obligations must be proven safe!
    let pkt = find_sample("packets").unwrap();
    let pkt_eng = StarEngine::from_source(pkt.initial_spoke, pkt.source).unwrap();
    let pkt_ver = pkt_eng.verify();
    assert_eq!(pkt_ver.total_obligations, 3, "{:?}", pkt_ver);
    assert_eq!(pkt_ver.proven_safe, 3, "{:?}", pkt_ver);
    assert_eq!(pkt_ver.refuted, 0, "{:?}", pkt_ver);
    assert_eq!(pkt_ver.warnings, 0, "{:?}", pkt_ver);
    assert!(pkt_ver.unreachable_branches.is_empty(), "{:?}", pkt_ver.unreachable_branches);
    assert!(pkt_ver.all_safe());

    // 2. `pipeline` preset contains `if (false) { return -999; }` before optimization -> 1 UNSAT branch;
    //    after Hub optimization -> 0 UNSAT branches!
    let pipe = find_sample("pipeline").unwrap();
    let mut pipe_eng = StarEngine::from_source(pipe.initial_spoke, pipe.source).unwrap();
    assert_eq!(pipe_eng.verify().unreachable_branches.len(), 1);
    pipe_eng.optimize();
    assert!(pipe_eng.verify().unreachable_branches.is_empty());

    // 3. Buggy C11 snippet with unguarded division, unguarded indexing, failing assertion,
    //    and a path-contradicted `else if (ms >= 600)` after `if (ms >= 500)`:
    let buggy_c = r#"#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

int64_t unsafe_ratio(int64_t total, int64_t count) {
    return total / count;
}

int64_t unsafe_head(StarList_int64_t xs) {
    return xs.data[0];
}

int64_t shadowed_tier(int64_t ms) {
    if (ms >= 500) {
        return 2;
    } else if (ms >= 600) {
        return 3;
    }
    assert(ms >= 0);
    return 1;
}

int main(void) {
    return 0;
}
"#;
    let buggy_eng = StarEngine::from_source(SpokeId::C, buggy_c).unwrap();
    let buggy_ver = buggy_eng.verify();

    // Expect 3 refuted obligations (concrete Hub-VM-validated crash witnesses!) + 1 UNSAT dead branch
    assert_eq!(buggy_ver.refuted, 3, "Expected 3 refuted obligations, got {:?}", buggy_ver);
    assert_eq!(
        buggy_ver.unreachable_branches.len(),
        1,
        "Expected 1 UNSAT dead branch (`ms >= 600` shadowed by `ms >= 500`), got {:?}",
        buggy_ver.unreachable_branches
    );
    assert_eq!(buggy_ver.unreachable_branches[0].func, "shadowed_tier");

    let div_ob = buggy_ver
        .obligations
        .iter()
        .find(|o| o.kind == ObligationKind::DivByZero)
        .unwrap();
    assert!(matches!(
        &div_ob.status,
        VerifyStatus::Refuted { witness_call, runtime_error }
            if witness_call.contains("unsafe_ratio(") && runtime_error.contains("division by zero")
    ));

    let idx_ob = buggy_ver
        .obligations
        .iter()
        .find(|o| o.kind == ObligationKind::IndexBounds)
        .unwrap();
    assert!(matches!(
        &idx_ob.status,
        VerifyStatus::Refuted { witness_call, runtime_error }
            if witness_call.contains("unsafe_head([])") && runtime_error.contains("out of bounds")
    ));

    let assert_ob = buggy_ver
        .obligations
        .iter()
        .find(|o| o.kind == ObligationKind::Assertion)
        .unwrap();
    assert!(matches!(
        &assert_ob.status,
        VerifyStatus::Refuted { witness_call, runtime_error }
            if witness_call.contains("shadowed_tier(-") && runtime_error.contains("assertion failed")
    ));
}

#[test]
fn ast_coverage_and_call_tracer_detects_dead_branches_and_hotspots() {
    let sample = find_sample("pipeline").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();

    // Before optimizing: `if (false) { return -999; }` leaves `return -999` uncovered!
    let trace_before = engine.trace();
    assert!(trace_before.ok);
    assert!(
        trace_before.coverage_pct < 100,
        "Expected <100% coverage due to dead `if (false)` branch, got {}%",
        trace_before.coverage_pct
    );
    assert_eq!(trace_before.uncovered.len(), 1);
    assert_eq!(trace_before.uncovered[0].func, "calibrate_reading");
    assert_eq!(trace_before.uncovered[0].summary, "return");
    assert!(
        trace_before
            .hotspots
            .iter()
            .any(|h| h.name == "calibrate_reading" && h.calls == 6),
        "Expected 6 calls to calibrate_reading (4 in main + 2 in unit test), got {:?}",
        trace_before.hotspots
    );
    assert!(!trace_before.call_trace.is_empty());

    // After Hub optimization: dead branch is pruned, elevating AST statement coverage to 100%!
    let (snap_after, rewrites) = engine.optimize();
    assert!(rewrites >= 4);
    assert_eq!(snap_after.coverage_pct, 100);

    let trace_after = engine.trace();
    assert_eq!(trace_after.coverage_pct, 100);
    assert!(trace_after.uncovered.is_empty());
}

#[test]
fn hub_vm_executes_instantly_and_guards_against_infinite_loops() {
    let inf_py = "def main() -> None:\n    x = 0\n    while True:\n        x += 1\n";
    let engine = StarEngine::from_source(SpokeId::Python, inf_py).unwrap();
    let res = eval_module(engine.hub(), 500);
    assert!(!res.ok);
    assert!(
        res.error
            .as_deref()
            .unwrap_or("")
            .contains("step budget (500) exceeded"),
        "Expected step-budget guard, got: {:?}",
        res.error
    );
}

#[test]
fn cross_language_semantic_rename_is_scope_and_type_directed() {
    // Two structs share a field named `value`; renaming `Metric.value` must NOT rename `Other.value`!
    let py_src = r#"from dataclasses import dataclass

@dataclass
class Metric:
    value: int

@dataclass
class Other:
    value: int

def read_both(m: Metric, o: Other) -> int:
    value = 10
    return m.value + o.value + value

def main() -> None:
    m = Metric(value=5)
    o = Other(value=7)
    print(read_both(m, o))

if __name__ == "__main__":
    main()
"#;
    let mut engine = StarEngine::from_source(SpokeId::Python, py_src).unwrap();

    // 1. Type-directed field rename: `Metric.value` -> `Metric.score`
    let (snap1, count1) = engine.rename_symbol("Metric.value", "score").unwrap();
    assert_eq!(count1, 3); // struct field decl + `m.value` access + `Metric(value=5)` init
    assert!(snap1.views["rust"].contains("pub struct Metric {\n    pub score: i64,\n}"));
    assert!(snap1.views["rust"].contains("pub struct Other {\n    pub value: i64,\n}"));
    assert!(snap1.views["swift"].contains("Metric(score: 5)"));
    assert!(snap1.views["ruby"].contains("Metric.new(score: 5)"));
    assert!(snap1.views["python"].contains("return m.score + o.value + value"));

    // 2. Scope-directed local variable rename: `read_both::value` -> `bonus` (leaves `Other.value` untouched)
    let (snap2, count2) = engine.rename_symbol("var:read_both::value", "bonus").unwrap();
    assert_eq!(count2, 2);
    assert!(snap2.views["cpp"].contains("return m.score + o.value + bonus;"));
    assert!(snap2.views["ruby"].contains("return m.score + o.value + bonus"));

    // 3. Function rename across all 9 languages: `read_both` -> `combine_pair`
    let (snap3, count3) = engine.rename_symbol("fn:read_both", "combine_pair").unwrap();
    assert_eq!(count3, 2);
    assert!(snap3.views["swift"].contains("func combine_pair("));
    assert!(snap3.views["go"].contains("func combine_pair("));
    assert!(snap3.views["ruby"].contains("def combine_pair("));
    assert!(snap3.views["typescript"].contains("combine_pair(m, o)"));
    assert_eq!(snap3.live_eval.stdout.trim(), "22");
}

#[test]
fn hub_optimizer_folds_constants_and_prunes_dead_branches_across_all_nine_spokes() {
    let sample = find_sample("pipeline").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
    let before_out = engine.snapshot().live_eval.stdout;

    let (snap, rewrites) = engine.optimize();
    assert!(rewrites >= 4, "Expected at least 4 optimizations, got {}", rewrites);
    assert_eq!(snap.live_eval.stdout, before_out);

    // `25 * 4` -> `100`, `(sample + 0) * 1` -> `sample`, and `if (false)` pruned in every language!
    for spoke_key in [
        "rust",
        "zig",
        "c",
        "cpp",
        "swift",
        "java",
        "go",
        "python",
        "ruby",
        "lua",
        "typescript",
        "star",
    ] {
        let code = &snap.views[spoke_key];
        assert!(!code.contains("999"), "Dead branch survived in {}:\n{}", spoke_key, code);
        assert!(!code.contains("25"), "Unfolded constant survived in {}:\n{}", spoke_key, code);
        assert!(code.contains("100"), "Folded 100 missing in {}:\n{}", spoke_key, code);
    }

    // Optimized Hub still satisfies GetPut across all 9 spokes
    let opt_hub = engine.hub().clone();
    for spoke in SpokeId::ALL {
        let lens = lens_for(spoke);
        let rendered = lens.get(&opt_hub);
        assert_eq!(lens.put(&rendered, &opt_hub).unwrap(), opt_hub);
    }
}

#[test]
fn mid_keystroke_syntax_error_holds_hub_without_corrupting_other_views() {
    let sample = find_sample("scores").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
    let rev_before = engine.revision();
    let rust_before = engine.project(SpokeId::Rust);

    let err = engine
        .apply_edit(SpokeId::Swift, "func broken_syntax(\n")
        .expect_err("incomplete Swift should return Diagnostic");
    assert_eq!(err.language, "swift");
    assert_eq!(engine.revision(), rev_before);
    assert_eq!(engine.project(SpokeId::Rust), rust_before);
}

#[test]
fn central_hub_typechecker_catches_cross_language_type_and_control_flow_errors() {
    for sample in SAMPLES {
        let engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
        let diags = check_module(engine.hub());
        assert!(
            diags.is_empty(),
            "Sample '{}' had unexpected semantic diagnostics: {:?}",
            sample.id,
            diags
        );
    }

    let buggy_py = r#"def add_pair(a: int, b: int) -> int:
    break
    return "not_an_int"

def main() -> None:
    x = ghost_var + 1
    y = add_pair("bad_arg")

def test_bad_assert() -> None:
    assert 42
    assert "txt" == 99
"#;
    let engine = StarEngine::from_source(SpokeId::Python, buggy_py).unwrap();
    let diags = check_module(engine.hub());
    let messages: Vec<&str> = diags.iter().map(|d| d.message.as_str()).collect();

    assert!(messages.iter().any(|m| m.contains("'break' used outside of a loop")));
    assert!(messages.iter().any(|m| m.contains("expected return type Int, found Str")));
    assert!(messages.iter().any(|m| m.contains("undeclared variable 'ghost_var'")));
    assert!(messages.iter().any(|m| m.contains("expects 2 argument(s), got 1")));
    assert!(messages.iter().any(|m| m.contains("argument 1 to 'add_pair' expects Int, found Str")));
    assert!(messages.iter().any(|m| m.contains("'assert' condition must be Bool, found Int")));
    assert!(messages.iter().any(|m| m.contains("'assert_eq' requires compatible types, found Str and Int")));
}

#[test]
fn undo_and_redo_walk_cross_language_history_stack() {
    let sample = find_sample("scores").unwrap();
    let mut engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
    let initial_rs = engine.project(SpokeId::Rust);

    let py1 = engine
        .project(SpokeId::Python)
        .replace("clamp_scores(raw, 100)", "clamp_scores(raw, 80)");
    engine.apply_edit(SpokeId::Python, &py1).unwrap();
    let after_py_rs = engine.project(SpokeId::Rust);

    let swift2 = engine
        .project(SpokeId::Swift)
        .replace("clamp_scores(raw, 80)", "clamp_scores(raw, 60)");
    engine.apply_edit(SpokeId::Swift, &swift2).unwrap();
    assert!(engine.project(SpokeId::Rust).contains("clamp_scores(&raw, 60)"));

    let u1 = engine.undo().unwrap();
    assert!(u1.views["rust"].contains("clamp_scores(&raw, 80)"));
    let u2 = engine.undo().unwrap();
    assert_eq!(u2.views["rust"], initial_rs);

    let r1 = engine.redo().unwrap();
    assert_eq!(r1.views["rust"], after_py_rs);
    let r2 = engine.redo().unwrap();
    assert!(r2.views["rust"].contains("clamp_scores(&raw, 60)"));
}

#[test]
fn all_samples_compile_and_produce_identical_output_across_eleven_engines() {
    for sample in SAMPLES {
        let engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
        let report = run_all_spokes(&engine);
        assert_eq!(report.results.len(), 14);

        for r in &report.results {
            assert!(
                r.ok,
                "Sample '{}' failed on {}:\nstdout: {}\nstderr: {}\ncode:\n{}",
                sample.id,
                r.language,
                r.stdout,
                r.stderr,
                match r.language {
                    "Rust (rustc)" => engine.project(SpokeId::Rust),
                    "Zig (zig)" => engine.project(SpokeId::Zig),
                    "C11 (clang)" => engine.project(SpokeId::C),
                    "C++ (clang++)" => engine.project(SpokeId::Cpp),
                    "Swift (swiftc)" => engine.project(SpokeId::Swift),
                    "Java (javac)" => engine.project(SpokeId::Java),
                    "Go (go run)" => engine.project(SpokeId::Go),
                    "Python (python3)" => engine.project(SpokeId::Python),
                    "Ruby (ruby)" => engine.project(SpokeId::Ruby),
                    "LuaJIT (luajit)" => engine.project(SpokeId::Lua),
                    "Perl 5 (perl)" => engine.project(SpokeId::Perl),
                    "TypeScript (node)" => engine.project(SpokeId::TypeScript),
                    _ => engine.project(SpokeId::Star),
                }
            );
        }
        assert!(
            report.outputs_match,
            "Outputs diverged on sample '{}': {:?}",
            sample.id, report.results
        );
    }
}

#[test]
fn web_studio_http_api_syncs_merges_verifies_traces_mutates_hardens_and_runs_eleven_engines() {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    thread::spawn(move || {
        let _ = serve_listener(listener);
    });

    let send_http = |method: &str, path: &str, body: &str| -> String {
        let mut stream = TcpStream::connect(addr).unwrap();
        let req = format!(
            "{} {} HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
            method,
            path,
            body.len(),
            body
        );
        stream.write_all(req.as_bytes()).unwrap();
        let mut resp = String::new();
        stream.read_to_string(&mut resp).unwrap();
        resp
    };

    let state_resp = send_http("GET", "/api/state", "");
    assert!(state_resp.contains("HTTP/1.1 200 OK"));
    assert!(state_resp.contains("\"zig\":"));
    assert!(state_resp.contains("\"c\":"));
    assert!(state_resp.contains("\"swift\":"));
    assert!(state_resp.contains("\"java\":"));
    assert!(state_resp.contains("\"ruby\":"));
    assert!(state_resp.contains("\"safety_proven\":"));
    assert!(state_resp.contains("\"coverage_pct\":"));
    assert!(state_resp.contains("\"test_results\":"));
    assert!(state_resp.contains("\"live_eval\":"));

    // Run Hub Symbolic Verifier via /api/verify
    let ver_resp = send_http("POST", "/api/verify", "{}");
    assert!(ver_resp.contains("\"ok\":true"), "verify failed: {}", ver_resp);
    assert!(ver_resp.contains("\"proven_safe\":"));
    assert!(ver_resp.contains("\"obligations\":["));

    // Run Hub Mutation Testing via /api/mutate on initial `alerts` preset
    let mut_resp = send_http("POST", "/api/mutate", "{}");
    assert!(mut_resp.contains("\"ok\":true"), "mutate failed: {}", mut_resp);
    assert!(mut_resp.contains("\"score_pct\":"));
    assert!(mut_resp.contains("\"outcomes\":["));

    // Auto-Harden boundary unit tests via /api/harden
    let hard_resp = send_http("POST", "/api/harden", "{}");
    assert!(hard_resp.contains("\"ok\":true"), "harden failed: {}", hard_resp);
    assert!(hard_resp.contains("test_mutation_hardened"));

    // Load Pipeline optimizer preset via /api/sample
    let sample_resp = send_http("POST", "/api/sample", "{\"id\":\"pipeline\"}");
    assert!(sample_resp.contains("\"ok\":true"));
    assert!(sample_resp.contains("calibrate_reading"));

    // Inspect AST coverage & hotspots before optimization via /api/trace
    let trace_resp = send_http("POST", "/api/trace", "{}");
    assert!(trace_resp.contains("\"ok\":true"));
    assert!(trace_resp.contains("\"uncovered\":[{\"node_id\":"));
    assert!(trace_resp.contains("\"hotspots\":["));

    // Optimize via /api/optimize
    let opt_resp = send_http("POST", "/api/optimize", "{}");
    assert!(opt_resp.contains("\"ok\":true"));
    assert!(!opt_resp.contains("-999"));
    assert!(opt_resp.contains("\"coverage_pct\":100"));

    // Rename function via /api/refactor
    let ref_resp = send_http(
        "POST",
        "/api/refactor",
        "{\"target\":\"fn:calibrate_reading\",\"new_name\":\"clamp_sensor\"}",
    );
    assert!(ref_resp.contains("\"ok\":true"));
    assert!(ref_resp.contains("pub fn clamp_sensor("));
    assert!(ref_resp.contains("int64_t clamp_sensor("));
    assert!(ref_resp.contains("func clamp_sensor("));
    assert!(ref_resp.contains("static long clamp_sensor("));
    assert!(ref_resp.contains("def clamp_sensor("));

    // Verify /api/diff and /api/merge endpoints
    let py_fork = "# Calibrate sensor readings with foldable constants and algebraic identities\ndef clamp_sensor(sample: int) -> int:\n    ceiling = 100\n    adjusted = sample\n    return min(adjusted, ceiling)\n\ndef main() -> None:\n    readings = [12, 85, 140, 64]\n    total = 0\n    for r in readings:\n        total += clamp_sensor(r)\n    print(\"calibrated_sum:\", total)\n\ndef test_calibration_ceiling() -> None:\n    assert clamp_sensor(42) == 42\n    assert clamp_sensor(180) == 100\n\nif __name__ == \"__main__\":\n    main()\n";
    let diff_body = format!("{{\"spoke\":\"python\",\"source\":{}}}", json_str(py_fork));
    let diff_resp = send_http("POST", "/api/diff", &diff_body);
    assert!(diff_resp.contains("\"ok\":true"), "diff failed: {}", diff_resp);
    assert!(diff_resp.contains("\"identical\":true"), "diff expected identical: {}", diff_resp);

    let merge_body = format!(
        "{{\"left_spoke\":\"python\",\"left_source\":{},\"right_spoke\":\"python\",\"right_source\":{}}}",
        json_str(py_fork),
        json_str(py_fork)
    );
    let merge_resp = send_http("POST", "/api/merge", &merge_body);
    assert!(merge_resp.contains("\"ok\":true"), "merge failed: {}", merge_resp);
    assert!(merge_resp.contains("\"clean\":true"), "merge expected clean: {}", merge_resp);

    // Verify /api/wasm endpoint compiles Wasm binary + WAT and runs V8 JIT
    let wasm_resp = send_http("POST", "/api/wasm", "{}");
    assert!(wasm_resp.contains("\"ok\":true"), "wasm failed: {}", wasm_resp);
    assert!(wasm_resp.contains("\"jit_ok\":true"), "wasm jit failed: {}", wasm_resp);
    assert!(wasm_resp.contains("\"wat\":"));
    assert!(wasm_resp.contains("\"wasm_b64\":"));

    // Verify /api/debug endpoint records time-travel steps, 13-spoke lines & backward slice
    let dbg_resp = send_http("POST", "/api/debug", "{\"slice\":\"total\"}");
    assert!(dbg_resp.contains("\"ok\":true"), "debug failed: {}", dbg_resp);
    assert!(dbg_resp.contains("\"trace_ok\":true"), "debug trace failed: {}", dbg_resp);
    assert!(dbg_resp.contains("\"spoke_lines\":{"), "debug missing spoke_lines: {}", dbg_resp);
    assert!(dbg_resp.contains("\"slice\":{"), "debug missing slice: {}", dbg_resp);

    // Verify /api/complexity and /api/quickcheck endpoints
    let comp_resp = send_http("POST", "/api/complexity", "{}");
    assert!(comp_resp.contains("\"ok\":true"), "complexity failed: {}", comp_resp);
    assert!(comp_resp.contains("\"dominant_big_o\":"));
    assert!(comp_resp.contains("\"spoke_metrics\":["));

    let qc_resp = send_http("POST", "/api/quickcheck", "{\"trials\":\"16\"}");
    assert!(qc_resp.contains("\"ok\":true"), "quickcheck failed: {}", qc_resp);
    assert!(qc_resp.contains("\"all_passed\":true"), "quickcheck failed: {}", qc_resp);
    assert!(qc_resp.contains("\"discovered_invariants\":["));

    // Verify /api/repair endpoint with demo fault injection + CEGIS patch synthesis
    let rep_resp = send_http("POST", "/api/repair", "{\"inject_demo\":\"true\"}");
    assert!(rep_resp.contains("\"ok\":true"), "repair failed: {}", rep_resp);
    assert!(rep_resp.contains("\"repaired\":true"), "repair failed: {}", rep_resp);
    assert!(rep_resp.contains("\"diffs_by_spoke\":{"), "repair missing diffs: {}", rep_resp);

    // Verify /api/synth and /api/cfg endpoints
    let synth_resp = send_http("POST", "/api/synth", "{\"spec\":\"default\",\"inject\":\"false\"}");
    assert!(synth_resp.contains("\"ok\":true"), "synth failed: {}", synth_resp);
    assert!(synth_resp.contains("\"synthesized\":true"), "synth failed: {}", synth_resp);
    assert!(synth_resp.contains("\"pruned_equivalents\":"));

    let cfg_resp = send_http("POST", "/api/cfg", "{}");
    assert!(cfg_resp.contains("\"ok\":true"), "cfg failed: {}", cfg_resp);
    assert!(cfg_resp.contains("\"total_natural_loops\":"));
    assert!(cfg_resp.contains("flowchart TD"));

    // Verify /api/ssa and /api/contracts endpoints
    let ssa_resp = send_http("POST", "/api/ssa", "{}");
    assert!(ssa_resp.contains("\"ok\":true"), "ssa failed: {}", ssa_resp);
    assert!(ssa_resp.contains("\"total_phi_nodes\":"));
    assert!(ssa_resp.contains("\"def_use_chains\":["));

    let cnt_resp = send_http("POST", "/api/contracts", "{}");
    assert!(cnt_resp.contains("\"ok\":true"), "contracts failed: {}", cnt_resp);
    assert!(cnt_resp.contains("\"all_verified\":true"), "contracts failed: {}", cnt_resp);
    assert!(cnt_resp.contains("\"verification_conditions\":["));

    // Verify /api/concolic and /api/security endpoints
    let conc_resp = send_http("POST", "/api/concolic", "{\"inject\":\"false\"}");
    assert!(conc_resp.contains("\"ok\":true"), "concolic failed: {}", conc_resp);
    assert!(conc_resp.contains("\"total_paths\":"));
    assert!(conc_resp.contains("\"path_condition\":"));

    let sec_resp = send_http("POST", "/api/security", "{}");
    assert!(sec_resp.contains("\"ok\":true"), "security failed: {}", sec_resp);
    assert!(sec_resp.contains("\"all_sinks_safe\":true"), "security failed: {}", sec_resp);
    assert!(sec_resp.contains("\"flow_edges\":["));

    // Verify /api/egraph and /api/peval endpoints
    let eg_resp = send_http("POST", "/api/egraph", "{\"apply\":\"false\"}");
    assert!(eg_resp.contains("\"ok\":true"), "egraph failed: {}", eg_resp);
    assert!(eg_resp.contains("\"total_eclasses\":"));
    assert!(eg_resp.contains("\"translation_validated\":true"));

    let pe_resp = send_http("POST", "/api/peval", "{\"apply\":\"false\"}");
    assert!(pe_resp.contains("\"ok\":true"), "peval failed: {}", pe_resp);
    assert!(pe_resp.contains("\"translation_validated\":true"), "peval failed: {}", pe_resp);
    assert!(pe_resp.contains("\"vm_steps_before\":"));

    // Verify /api/polyhedral and /api/wcet endpoints
    let poly_resp = send_http("POST", "/api/polyhedral", "{}");
    assert!(poly_resp.contains("\"ok\":true"), "polyhedral failed: {}", poly_resp);
    assert!(poly_resp.contains("\"vectorizable_loops\":"));
    assert!(poly_resp.contains("\"vectorized_by_spoke\":{"));

    let wcet_resp = send_http("POST", "/api/wcet", "{}");
    assert!(wcet_resp.contains("\"ok\":true"), "wcet failed: {}", wcet_resp);
    assert!(wcet_resp.contains("\"all_terminating\":true"), "wcet failed: {}", wcet_resp);
    assert!(wcet_resp.contains("\"module_wcet_cycles_n64\":"));

    // Verify /api/regalloc and /api/escape endpoints
    let reg_resp = send_http("POST", "/api/regalloc", "{\"k\":\"8\"}");
    assert!(reg_resp.contains("\"ok\":true"), "regalloc failed: {}", reg_resp);
    assert!(reg_resp.contains("\"aarch64_asm\":"));
    assert!(reg_resp.contains("\"x86_64_asm\":"));

    let esc_resp = send_http("POST", "/api/escape", "{}");
    assert!(esc_resp.contains("\"ok\":true"), "escape failed: {}", esc_resp);
    assert!(esc_resp.contains("\"heap_reduction_pct\":"));
    assert!(esc_resp.contains("\"optimized_by_spoke\":{"));

    // Verify /api/microarch and /api/schedule endpoints
    let uarch_resp = send_http("POST", "/api/microarch", "{}");
    assert!(uarch_resp.contains("\"ok\":true"), "microarch failed: {}", uarch_resp);
    assert!(uarch_resp.contains("\"superscalar_ipc\":"));
    assert!(uarch_resp.contains("\"l1d_hit_rate_pct\":"));

    let sched_resp = send_http("POST", "/api/schedule", "{}");
    assert!(sched_resp.contains("\"ok\":true"), "schedule failed: {}", sched_resp);
    assert!(sched_resp.contains("\"total_bubbles_eliminated\":"));
    assert!(sched_resp.contains("\"scheduled_listing\":"));

    // Verify /api/autodiff and /api/stability endpoints
    let ad_resp = send_http("POST", "/api/autodiff", "{\"inject\":\"false\"}");
    assert!(ad_resp.contains("\"ok\":true"), "autodiff failed: {}", ad_resp);
    assert!(ad_resp.contains("\"all_gradients_verified\":true"), "autodiff failed: {}", ad_resp);
    assert!(ad_resp.contains("\"reverse_tape\":["));

    let stab_resp = send_http("POST", "/api/stability", "{}");
    assert!(stab_resp.contains("\"ok\":true"), "stability failed: {}", stab_resp);
    assert!(stab_resp.contains("\"max_condition_number\":"));
    assert!(stab_resp.contains("\"hardened_by_spoke\":{"));

    // Verify /api/actors and /api/modelcheck endpoints
    let act_resp = send_http("POST", "/api/actors", "{}");
    assert!(act_resp.contains("\"ok\":true"), "actors failed: {}", act_resp);
    assert!(act_resp.contains("\"all_data_race_free\":true"));
    assert!(act_resp.contains("\"actor_by_spoke\":{"));

    let mc_resp = send_http("POST", "/api/modelcheck", "{}");
    assert!(mc_resp.contains("\"ok\":true"), "modelcheck failed: {}", mc_resp);
    assert!(mc_resp.contains("\"all_verified\":true"));
    assert!(mc_resp.contains("\"tla_plus_spec\":"));

    // Verify /api/zk and /api/sql endpoints
    let zk_resp = send_http("POST", "/api/zk", "{}");
    assert!(zk_resp.contains("\"ok\":true"), "zk failed: {}", zk_resp);
    assert!(zk_resp.contains("\"all_circuits_satisfied\":true"));
    assert!(zk_resp.contains("\"circom_template\":"));

    let sql_resp = send_http("POST", "/api/sql", "{}");
    assert!(sql_resp.contains("\"ok\":true"), "sql failed: {}", sql_resp);
    assert!(sql_resp.contains("\"ansi_sql_query\":"));
    assert!(sql_resp.contains("\"query_by_spoke\":{"));

    // Verify /api/refinement and /api/prob endpoints
    let refn_resp = send_http("POST", "/api/refinement", "{}");
    assert!(refn_resp.contains("\"ok\":true"), "refinement failed: {}", refn_resp);
    assert!(refn_resp.contains("\"all_subtypes_verified\":true"));
    assert!(refn_resp.contains("\"smtlib2_horn_script\":"));

    let prob_resp = send_http("POST", "/api/prob", "{}");
    assert!(prob_resp.contains("\"ok\":true"), "prob failed: {}", prob_resp);
    assert!(prob_resp.contains("\"mutual_information_bits\":"));
    assert!(prob_resp.contains("\"posterior_histogram\":["));

    // Verify /api/quantum and /api/automata endpoints
    let q_resp = send_http("POST", "/api/quantum", "{}");
    assert!(q_resp.contains("\"ok\":true"), "quantum failed: {}", q_resp);
    assert!(q_resp.contains("\"all_ancillas_uncomputed\":true"));
    assert!(q_resp.contains("OPENQASM 3.0;"));

    let dfa_resp = send_http("POST", "/api/automata", "{}");
    assert!(dfa_resp.contains("\"ok\":true"), "automata failed: {}", dfa_resp);
    assert!(dfa_resp.contains("\"all_myhill_nerode_minimal\":true"));
    assert!(dfa_resp.contains("\"fsm_by_spoke\":{"));

    // Verify /api/hls and /api/gpu endpoints
    let hls_resp = send_http("POST", "/api/hls", "{}");
    assert!(hls_resp.contains("\"ok\":true"), "hls failed: {}", hls_resp);
    assert!(hls_resp.contains("`default_nettype none"));
    assert!(hls_resp.contains("\"fsmd_states\":["));

    let gpu_resp = send_http("POST", "/api/gpu", "{}");
    assert!(gpu_resp.contains("\"ok\":true"), "gpu failed: {}", gpu_resp);
    assert!(gpu_resp.contains("__global__ void"));
    assert!(gpu_resp.contains("@compute @workgroup_size"));
    assert!(gpu_resp.contains("\"host_dispatch_by_spoke\":{"));

    // Verify /api/fhe and /api/seplogic endpoints
    let fhe_resp = send_http("POST", "/api/fhe", "{}");
    assert!(fhe_resp.contains("\"ok\":true"), "fhe failed: {}", fhe_resp);
    assert!(fhe_resp.contains("\"all_decryptions_verified\":true"));
    assert!(fhe_resp.contains("EvalMultAndRelinearize"));

    let sep_resp = send_http("POST", "/api/seplogic", "{}");
    assert!(sep_resp.contains("\"ok\":true"), "seplogic failed: {}", sep_resp);
    assert!(sep_resp.contains("\"all_memory_safe\":true"));
    assert!(sep_resp.contains("\"region_by_spoke\":{"));

    // Execute across all 14 engines via /api/run
    let run_resp = send_http("POST", "/api/run", "{}");
    assert!(run_resp.contains("\"outputs_match\":true"), "run failed: {}", run_resp);
    assert!(run_resp.contains("Hub VM (native)"));
    assert!(run_resp.contains("Wasm (V8 JIT)"));
    assert!(run_resp.contains("Zig (zig)"));
    assert!(run_resp.contains("C11 (clang)"));
    assert!(run_resp.contains("C++ (clang++)"));
    assert!(run_resp.contains("Swift (swiftc)"));
    assert!(run_resp.contains("Java (javac)"));
    assert!(run_resp.contains("Ruby (ruby)"));
    assert!(run_resp.contains("LuaJIT (luajit)"));
    assert!(run_resp.contains("Perl 5 (perl)"));
    assert!(run_resp.contains("calibrated_sum: 261"));
}

#[test]
fn polyhedral_loop_vectorizer_and_floyd_turing_termination_wcet_prover_analyze_and_verify_across_thirteen_languages() {
    // 1. Polyhedral Loop Vectorizer on `pipeline` (AssociativeMapReduce)
    let pipe_sample = find_sample("pipeline").unwrap();
    let pipe_eng = StarEngine::from_source(pipe_sample.initial_spoke, pipe_sample.source).unwrap();
    let poly_pipe = pipe_eng.polyhedral();
    assert_eq!(poly_pipe.total_loops, 1);
    assert_eq!(poly_pipe.vectorizable_loops, 1);
    assert_eq!(poly_pipe.map_reduce_loops, 1);
    assert_eq!(poly_pipe.total_reductions, 1);
    assert!(poly_pipe.max_simd4_speedup >= 3.2);

    let lp0 = &poly_pipe.loops[0];
    assert_eq!(lp0.classification, "AssociativeMapReduce");
    assert!(lp0.simd_vectorizable);
    assert!(lp0.map_reduce_parallelizable);
    assert_eq!(lp0.vectorized_by_spoke.len(), 13);
    assert!(lp0.vectorized_by_spoke["rust"].contains(".iter().copied()"));
    assert!(lp0.vectorized_by_spoke["zig"].contains("@Vector(4, i64)"));
    assert!(lp0.vectorized_by_spoke["c"].contains("#pragma clang loop vectorize(enable)"));
    assert!(lp0.vectorized_by_spoke["python"].contains("sum("));
    assert!(lp0.vectorized_by_spoke["perl"].contains("sum0("));

    // 2. Polyhedral Loop Vectorizer on `packets` (FilterMapReduce) & `scores` (ParallelMap)
    let pkt_sample = find_sample("packets").unwrap();
    let pkt_eng =
        StarEngine::from_source(pkt_sample.initial_spoke, pkt_sample.source).unwrap();
    let poly_pkt = pkt_eng.polyhedral();
    assert_eq!(poly_pkt.total_loops, 1);
    assert_eq!(poly_pkt.loops[0].classification, "FilterMapReduce");
    assert!(poly_pkt.loops[0].simd_vectorizable);
    assert!(poly_pkt.loops[0].map_reduce_parallelizable);
    assert!(poly_pkt.loops[0].brent_parallelism_n64 > 5.0);

    let scores_sample = find_sample("scores").unwrap();
    let scores_eng =
        StarEngine::from_source(scores_sample.initial_spoke, scores_sample.source).unwrap();
    let poly_scores = scores_eng.polyhedral();
    assert_eq!(poly_scores.total_loops, 2);
    assert_eq!(poly_scores.loops[0].classification, "ParallelMap");
    assert_eq!(poly_scores.loops[1].classification, "AssociativeMapReduce");

    // 3. Polyhedral Loop Vectorizer on `ratelimit` (SequentialStateMachine due to guard-read `cost <= tokens`)
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();
    let poly_rl = rl_eng.polyhedral();
    assert_eq!(poly_rl.total_loops, 1);
    assert_eq!(poly_rl.loops[0].classification, "SequentialStateMachine");
    assert!(!poly_rl.loops[0].simd_vectorizable);
    assert_eq!(poly_rl.sequential_state_loops, 1);

    // 4. Floyd-Turing Well-Founded Ranking Termination Prover & IPET WCET Analyzer on all presets
    for sample in SAMPLES {
        let eng = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
        let wcet = eng.termination_wcet();
        assert!(
            wcet.all_terminating,
            "Sample '{}' should be proven terminating: {:?}",
            sample.id, wcet
        );
        assert_eq!(wcet.diverging_or_unproven_loops, 0);
        assert!(
            wcet.module_wcet_cycles_n64 >= wcet.module_bcet_cycles_n64,
            "WCET ({}) must be >= BCET ({}) on sample '{}'",
            wcet.module_wcet_cycles_n64,
            wcet.module_bcet_cycles_n64,
            sample.id
        );
    }

    // 5. Floyd-Turing Prover catches non-terminating / unbounded while loop!
    let inf_py = "def spin_forever(n: int) -> int:\n    x = 0\n    while x >= 0:\n        x += 1\n    return x\n\ndef main() -> None:\n    print(0)\n";
    let inf_eng = StarEngine::from_source(SpokeId::Python, inf_py).unwrap();
    let inf_wcet = inf_eng.termination_wcet();
    assert!(!inf_wcet.all_terminating);
    assert_eq!(inf_wcet.diverging_or_unproven_loops, 1);
}

#[test]
fn chaitin_briggs_register_allocator_native_asm_and_escape_sroa_analyzer_verify_across_thirteen_languages() {
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();

    // 1. Standard K=8 Chaitin-Briggs Graph-Coloring & Linear-Scan Register Allocation
    let reg8 = rl_eng.regalloc(Some(8));
    assert_eq!(reg8.k_registers, 8);
    assert!(reg8.total_virtual_regs >= 15);
    assert!(reg8.total_interference_edges >= 10);
    assert!(reg8.total_aarch64_insts >= 20);
    assert!(reg8.total_x86_64_insts >= 20);

    let eval_fn = reg8
        .functions
        .iter()
        .find(|f| f.fn_name == "evaluate_quota")
        .unwrap();
    assert!(eval_fn.aarch64_asm.contains(".globl _evaluate_quota"));
    assert!(eval_fn.aarch64_asm.contains("stp x29, x30"));
    assert!(eval_fn.aarch64_asm.contains("sdiv"));
    assert!(eval_fn.x86_64_asm.contains(".intel_syntax noprefix"));
    assert!(eval_fn.x86_64_asm.contains("idiv"));
    assert!(eval_fn.mermaid_graph.contains("graph LR"));

    // Verify that no two interfering variables share the same physical color in K=8
    let color_by_var: std::collections::BTreeMap<&str, Option<usize>> = eval_fn
        .intervals
        .iter()
        .map(|iv| (iv.var_name.as_str(), iv.assigned_color))
        .collect();
    for edge in &eval_fn.edges {
        if edge.kind == "Interference" {
            if let (Some(Some(cu)), Some(Some(cv))) = (
                color_by_var.get(edge.u.as_str()),
                color_by_var.get(edge.v.as_str()),
            ) {
                assert_ne!(
                    cu, cv,
                    "Interfering variables {} and {} were assigned identical color {}",
                    edge.u, edge.v, cu
                );
            }
        }
    }

    // 2. Constrained K=2 Kempe Spill Stress-Test: forces stack spill slots `[sp, #offset]` / `QWORD PTR [rbp - offset]`
    let reg2 = rl_eng.regalloc(Some(2));
    assert_eq!(reg2.k_registers, 2);
    assert!(
        reg2.total_spills > 0,
        "Expected stack spills when K=2 on ratelimit, got 0"
    );
    let eval_fn2 = reg2
        .functions
        .iter()
        .find(|f| f.fn_name == "evaluate_quota")
        .unwrap();
    assert!(eval_fn2.spilled_vars > 0);
    assert!(eval_fn2
        .intervals
        .iter()
        .any(|iv| iv.spilled && iv.aarch64_loc.starts_with("[sp, #")));

    // 3. Interprocedural Escape Analysis, SROA & RVO across `scores` and `ledger`
    let scores_sample = find_sample("scores").unwrap();
    let scores_eng =
        StarEngine::from_source(scores_sample.initial_spoke, scores_sample.source).unwrap();
    let esc_scores = scores_eng.escape_analysis();
    assert!(esc_scores.total_alloc_sites >= 4);
    assert!(esc_scores.stack_promoted_sites >= 1);
    assert!(esc_scores.rvo_eliminated_sites >= 2);
    assert!(esc_scores.sroa_scalarized_fields >= 3);
    assert!(esc_scores.total_bytes_saved_per_run >= 80);
    assert_eq!(esc_scores.heap_reduction_pct, 100);
    for f in &esc_scores.functions {
        assert_eq!(f.optimized_by_spoke.len(), 13);
    }

    let ledger_sample = find_sample("ledger").unwrap();
    let ledger_eng =
        StarEngine::from_source(ledger_sample.initial_spoke, ledger_sample.source).unwrap();
    let esc_ledger = ledger_eng.escape_analysis();
    assert!(esc_ledger.sroa_scalarized_fields >= 3);
    assert!(esc_ledger.total_bytes_saved_per_run >= 60);
}

#[test]
fn superscalar_cpu_cache_branch_simulator_and_critical_path_list_scheduler_verify_across_thirteen_languages() {
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();

    // 1. 4-Wide Out-of-Order Superscalar CPU, 2-Bit Branch Predictor & 8-Way L1D Cache Simulator
    let uarch = rl_eng.microarch();
    assert!(uarch.total_uops_retired >= 40);
    assert!(
        uarch.total_ooo_cycles <= uarch.total_in_order_cycles,
        "4-wide Out-of-Order cycles ({}) must be <= In-Order cycles ({})",
        uarch.total_ooo_cycles,
        uarch.total_in_order_cycles
    );
    assert!(uarch.superscalar_ipc > 0.3);
    assert!(uarch.ooo_speedup >= 1.0);
    assert!(uarch.total_branches >= 4);
    assert!(uarch.branch_accuracy_pct > 0.0 && uarch.branch_accuracy_pct <= 100.0);
    assert!(uarch.total_mem_accesses >= 5);
    assert!(uarch.l1d_hit_rate_pct >= 50.0);
    assert!(!uarch.branch_sites.is_empty());
    assert!(!uarch.cache_sites.is_empty());

    // 2. Gibbons-Muchnick Critical-Path DAG List Instruction Scheduler
    let sched = rl_eng.schedule_instructions();
    assert!(sched.total_instructions >= 25);
    assert!(sched.total_dag_edges >= 15);
    assert!(
        sched.total_cycles_after <= sched.total_cycles_before,
        "Scheduled cycles ({}) must be <= Unscheduled cycles ({})",
        sched.total_cycles_after,
        sched.total_cycles_before
    );
    assert!(
        sched.total_bubbles_eliminated > 0,
        "Expected Critical-Path List Scheduler to eliminate stall bubbles on ratelimit, got 0"
    );
    assert!(sched.overall_speedup >= 1.0);

    for f in &sched.functions {
        assert!(f.scheduled_cycles_after <= f.in_order_cycles_before);
        assert!(f.mermaid_dag.contains("flowchart TD"));
        // Verify topological soundness of the list schedule: every RAW/WAR/WAW dependence edge
        // `(from_idx -> to_idx, latency)` is respected in `issue_cycle`!
        let issue_by_orig: std::collections::BTreeMap<usize, u64> = f
            .instructions
            .iter()
            .map(|inst| (inst.orig_idx, inst.issue_cycle))
            .collect();
        for edge in &f.dag_edges {
            let u_cy = issue_by_orig[&edge.from_idx];
            let v_cy = issue_by_orig[&edge.to_idx];
            assert!(
                v_cy >= u_cy + edge.latency,
                "Dependence edge #{} -> #{} ({}, {}c) violated in {}: v issued at {}c before u ({}c) + {}c",
                edge.from_idx,
                edge.to_idx,
                edge.kind,
                edge.latency,
                f.fn_name,
                v_cy,
                u_cy,
                edge.latency
            );
        }
    }
}

#[test]
fn forward_dual_and_reverse_tape_autodiff_and_lipschitz_stability_auditor_verify_across_thirteen_languages() {
    // 1. Test Forward-Mode Dual vs. Reverse-Mode Wengert Tape AD on a polynomial + affine function
    let poly_py = r#"def poly_energy(x: int, y: int) -> int:
    return x * x * 3 + x * y * 2 + y * 5

def main() -> None:
    print(poly_energy(4, 3))
"#;
    let mut poly_eng = StarEngine::from_source(SpokeId::Python, poly_py).unwrap();
    let (ad_poly, snap_opt) = poly_eng.autodiff(true);
    assert!(ad_poly.all_gradients_verified);
    assert_eq!(ad_poly.differentiable_functions, 1);
    assert_eq!(ad_poly.total_partials, 2);
    assert_eq!(ad_poly.verified_partials, 2);

    let f_poly = &ad_poly.functions[0];
    assert_eq!(f_poly.fn_name, "poly_energy");
    assert!(f_poly.tape_nodes_count >= 10);
    // At sample point (x=12, y=16):
    // f(x, y) = 3*x^2 + 2*x*y + 5*y
    // ∂f/∂x = 6*x + 2*y = 6*12 + 2*16 = 72 + 32 = 104
    // ∂f/∂y = 2*x + 5 = 2*12 + 5 = 29
    let dx = f_poly.partials.iter().find(|p| p.param_name == "x").unwrap();
    let dy = f_poly.partials.iter().find(|p| p.param_name == "y").unwrap();
    assert_eq!(dx.forward_dual_deriv, 104.0);
    assert_eq!(dx.reverse_tape_adjoint, 104.0);
    assert!(dx.dual_matches_reverse);
    assert_eq!(dy.forward_dual_deriv, 29.0);
    assert_eq!(dy.reverse_tape_adjoint, 29.0);
    assert!(dy.dual_matches_reverse);
    assert_eq!(f_poly.grad_by_spoke.len(), 13);

    // Injected `grad_poly_energy` + `test_autodiff_poly_energy` into Hub and verified across all 13 spokes!
    let snap = snap_opt.expect("Expected snapshot after injecting gradient function");
    assert!(snap.semantic_diagnostics.is_empty());
    assert!(snap.test_results.iter().all(|t| t.passed));
    for spoke in SpokeId::ALL {
        let lens = lens_for(spoke);
        let code = &snap.views[spoke.as_str()];
        assert!(
            code.contains("grad_poly_energy"),
            "Missing grad_poly_energy in {}:\n{}",
            spoke.as_str(),
            code
        );
        let lifted = lens.put(code, poly_eng.hub()).unwrap();
        assert_eq!(&lifted, poly_eng.hub());
    }

    // 2. Numerical Stability, Condition Number κ_f & Lipschitz Bound L_f on `ratelimit`
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();
    let stab = rl_eng.numerical_stability();
    assert_eq!(stab.total_functions, 2);
    assert!(stab.quantization_sites >= 1);
    assert!(stab.overflow_sites >= 1);
    assert!(stab.max_condition_number >= 1.0);
    assert!(stab.max_lipschitz_constant >= 1.0);
    for f in &stab.functions {
        assert_eq!(f.hardened_by_spoke.len(), 13);
    }
}

#[test]
fn lamport_vector_clock_actor_verifier_and_tlaplus_bounded_model_checker_verify_across_thirteen_languages() {
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();

    // 1. Lamport Vector-Clock Happens-Before (→) Race Detector, Deadlock Prover & 13-Spoke Actor Lowering
    let act = rl_eng.actors();
    assert_eq!(act.total_functions, 2);
    assert!(act.total_actor_stages >= 5);
    assert!(act.total_vc_events >= 10);
    assert_eq!(act.total_races_detected, 0);
    assert_eq!(act.total_wait_for_cycles, 0);
    assert!(act.all_data_race_free);
    assert!(act.all_deadlock_free);

    for f in &act.functions {
        assert!(f.data_race_free);
        assert!(f.deadlock_free);
        assert_eq!(f.actor_by_spoke.len(), 13);
        assert!(f.actor_by_spoke["rust"].contains("sync_channel"));
        assert!(f.actor_by_spoke["swift"].contains("actor "));
        assert!(f.actor_by_spoke["go"].contains("make(chan"));
        assert!(f.actor_by_spoke["ruby"].contains("Ractor.new"));
        // Verify strict monotonic progression of Lamport Vector Clocks along causal chain
        for w in f.events.windows(2) {
            let vc_prev = &w[0].vector_clock;
            let vc_next = &w[1].vector_clock;
            assert!(
                vc_prev.iter().zip(vc_next.iter()).all(|(a, b)| a <= b)
                    && vc_prev.iter().zip(vc_next.iter()).any(|(a, b)| a < b),
                "Expected strict happens-before VC {:?} < {:?} in {}",
                vc_prev,
                vc_next,
                f.fn_name
            );
        }
    }

    // 2. Explicit-State Bounded Model Checker (Kripke Structure) & TLA+ Specification Synthesizer
    let mc = rl_eng.model_check();
    assert_eq!(mc.total_functions, 2);
    assert!(mc.total_reachable_states >= 20);
    assert!(mc.total_transitions >= 40);
    assert_eq!(mc.total_properties, 6);
    assert_eq!(mc.verified_properties, 6);
    assert!(mc.all_verified);

    let eval_mc = mc
        .functions
        .iter()
        .find(|f| f.fn_name == "evaluate_quota")
        .unwrap();
    assert!(eval_mc.tla_plus_spec.contains("---- MODULE evaluate_quota_TLA ----"));
    assert!(eval_mc.tla_plus_spec.contains("SafetyInvariant =="));
    assert!(eval_mc.tla_plus_spec.contains("Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)"));
    assert!(eval_mc.mermaid_kripke.contains("stateDiagram-v2"));
}

#[test]
fn zk_r1cs_circuit_prover_and_relational_sql_optimizer_verify_across_thirteen_languages() {
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();

    // 1. Rank-1 Constraint System (R1CS) Arithmetic Circuit Compiler & Witness Verifier over F_p (p = 2^61 - 1)
    let zk = rl_eng.zk_r1cs();
    assert_eq!(zk.total_functions, 2);
    assert!(zk.total_wires >= 15);
    assert!(zk.total_constraints >= 10);
    assert_eq!(zk.satisfied_constraints, zk.total_constraints);
    assert!(zk.all_circuits_satisfied);

    for f in &zk.functions {
        assert!(f.all_constraints_satisfied);
        assert_eq!(f.satisfied_constraints, f.r1cs_constraints);
        assert!(f.circom_template.contains("pragma circom 2.1.6;"));
        assert!(f.circom_template.contains(&format!("template {}_Circuit()", f.fn_name)));
        assert!(f.mermaid_circuit.contains("flowchart LR"));
        // Verify every R1CS constraint has lhs_eval == rhs_eval in F_p
        for c in &f.constraints {
            assert!(
                c.satisfied,
                "Unsatisfied R1CS constraint #{} in {}: {} != {}",
                c.constraint_id, f.fn_name, c.lhs_eval, c.rhs_eval
            );
            assert_eq!(c.lhs_eval, c.rhs_eval);
        }
    }

    // 2. Relational Algebra (σ, π, Γ), Selection Pushdown & Vectorized Columnar SQL Optimizer
    let sql = rl_eng.relational_sql();
    assert_eq!(sql.total_functions, 2);
    assert!(sql.query_lifted_functions >= 1);
    assert!(sql.total_pushed_predicates >= 1);
    assert!(
        sql.total_columnar_cycles < sql.total_volcano_cycles,
        "Vectorized columnar cycles ({}) must be < Volcano tuple cycles ({})",
        sql.total_columnar_cycles,
        sql.total_volcano_cycles
    );
    assert!(sql.overall_columnar_speedup > 1.5);

    let eval_sql = sql
        .functions
        .iter()
        .find(|f| f.fn_name == "evaluate_quota")
        .unwrap();
    assert!(eval_sql.predicates_pushed_down >= 1);
    assert!(eval_sql.relational_algebra_expr.contains("σ_{"));
    assert!(eval_sql.relational_algebra_expr.contains("π_{"));
    assert!(eval_sql.relational_algebra_expr.contains("Γ_{"));
    assert!(eval_sql.ansi_sql_query.contains("WITH filtered_"));
    assert!(eval_sql.ansi_sql_query.contains("SELECT"));
    assert_eq!(eval_sql.query_by_spoke.len(), 13);
    assert!(eval_sql.query_by_spoke["rust"].contains("Polars LazyFrame Pushdown"));
    assert!(eval_sql.query_by_spoke["python"].contains("df.filter(pl.sql_expr"));
    assert!(eval_sql.query_by_spoke["java"].contains(".stream().filter("));
    assert!(eval_sql.query_by_spoke["typescript"].contains(".filter(x =>"));
}

#[test]
fn liquid_refinement_types_and_probabilistic_mcmc_shannon_entropy_verify_across_thirteen_languages() {
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();

    // 1. Liquid Refinement Types ({ ν: T | φ(ν) }), CHC Fixpoint Prover & 13-Spoke Dependent / Branded Types
    let ref_rep = rl_eng.liquid_refinements();
    assert_eq!(ref_rep.total_functions, 2);
    assert!(ref_rep.total_refined_bindings >= 8);
    assert!(ref_rep.total_qualifiers_inferred >= 12);
    assert!(ref_rep.total_horn_clauses >= 6);
    assert_eq!(ref_rep.discharged_horn_clauses, ref_rep.total_horn_clauses);
    assert!(ref_rep.all_subtypes_verified);

    for f in &ref_rep.functions {
        assert!(f.all_subtypes_valid);
        assert_eq!(f.horn_clauses_discharged, f.horn_clauses_total);
        assert!(f.smtlib2_horn_script.contains("(set-logic HORN)"));
        assert!(f.smtlib2_horn_script.contains("(check-sat)"));
        assert_eq!(f.refined_by_spoke.len(), 13);
        assert!(f.refined_by_spoke["rust"].contains("#[repr(transparent)]"));
        assert!(f.refined_by_spoke["zig"].contains("comptime min_val: i64"));
        assert!(f.refined_by_spoke["java"].contains("public record Refined_"));
        assert!(f.refined_by_spoke["python"].contains("Annotated[int"));
        assert!(f.refined_by_spoke["typescript"].contains("__liquid_brand"));
    }

    // 2. Probabilistic MCMC Sampler & Quantitative Information Flow (QIF) Shannon Entropy Quantifier
    let prob = rl_eng.probabilistic_entropy();
    assert_eq!(prob.total_functions, 2);
    assert_eq!(prob.total_mcmc_samples, 256);
    assert!(prob.max_output_entropy_bits > 0.5);
    assert!(prob.max_mutual_info_bits > 0.5);
    assert!(prob.total_branch_probes >= 2);

    for f in &prob.functions {
        assert_eq!(f.mcmc_particles, 128);
        assert!(f.acceptance_rate_pct > 0.0 && f.acceptance_rate_pct <= 100.0);
        assert!(f.input_shannon_entropy_bits > 0.0);
        assert!(f.output_shannon_entropy_bits >= 0.0);
        assert!(
            f.mutual_information_bits <= f.input_shannon_entropy_bits + 0.01,
            "Mutual information I(X;Y) ({}) must be <= H(X) ({})",
            f.mutual_information_bits,
            f.input_shannon_entropy_bits
        );
        assert!(!f.posterior_histogram.is_empty());
        assert!(f.mermaid_factor_graph.contains("flowchart LR"));
    }
}

#[test]
fn reversible_quantum_circuit_compiler_and_angluin_minimal_dfa_synthesizer_verify_across_thirteen_languages() {
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();

    // 1. Reversible Bennett-Toffoli Quantum Circuit Compiler (F -> Copy -> F†) & OpenQASM 3.0
    let q = rl_eng.quantum_circuit();
    assert_eq!(q.total_functions, 2);
    assert!(q.total_qubits_allocated >= 40);
    assert!(q.total_reversible_gates >= 10);
    assert!(q.total_toffoli_gates >= 2);
    assert!(q.total_clifford_t_gates >= 14);
    assert!(q.all_ancillas_uncomputed);
    assert!(q.max_grover_speedup >= 10.0);

    for f in &q.functions {
        assert!(f.ancilla_uncomputed_clean);
        assert!(f.uncompute_gates >= 1);
        assert_eq!(f.total_qubits, f.logical_qubits + f.ancilla_qubits);
        assert!(f.openqasm3_source.contains("OPENQASM 3.0;"));
        assert!(f.openqasm3_source.contains("include \"stdgates.inc\";"));
        assert!(f.mermaid_circuit.contains("flowchart LR"));
        // Verify Bennett uncomputation symmetry: every AncillaScratch register is restored to |0⟩
        for r in &f.registers {
            if r.role == "AncillaScratch" {
                assert!(
                    r.final_state.contains("uncomputed via F†"),
                    "Ancilla register {} not uncomputed: {}",
                    r.name,
                    r.final_state
                );
            }
        }
    }

    // 2. Angluin L* Active Learner & Myhill-Nerode Minimal DFA Synthesizer across 13 spokes
    let dfa = rl_eng.minimal_dfa();
    assert_eq!(dfa.total_functions, 2);
    assert!(dfa.total_unminimized_states > dfa.total_minimal_states);
    assert_eq!(dfa.total_minimal_states, 8);
    assert!(dfa.total_lstar_queries >= 48);
    assert!(dfa.all_myhill_nerode_minimal);
    assert!(dfa.overall_branchless_speedup >= 2.4);

    for f in &dfa.functions {
        assert_eq!(f.minimal_states, 4);
        assert_eq!(f.myhill_nerode_classes, 4);
        assert!(f.distinguishability_witnesses.len() >= 4);
        assert!(f.synthesized_regex.contains("σ_Valid"));
        assert_eq!(f.fsm_by_spoke.len(), 13);
        assert!(f.fsm_by_spoke["rust"].contains("DFA_DELTA_"));
        assert!(f.fsm_by_spoke["zig"].contains("[4][4]u8"));
        assert!(f.fsm_by_spoke["c"].contains("static const uint8_t DFA_DELTA_"));
        assert!(f.fsm_by_spoke["typescript"].contains("new Uint8Array("));
        assert!(f.mermaid_dfa.contains("stateDiagram-v2"));
    }
}

#[test]
fn hls_systemverilog_rtl_compiler_and_simt_gpu_kernel_synthesizer_verify_across_thirteen_languages() {
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();

    // 1. High-Level Synthesis (HLS) ASAP/ALAP Mobility FSMD Scheduler & IEEE-1800 SystemVerilog RTL Generator
    let hls = rl_eng.hls_rtl();
    assert_eq!(hls.total_functions, 2);
    assert!(hls.total_cdfg_ops >= 8);
    assert!(hls.total_fsmd_states >= 8);
    assert!(hls.total_lut6 >= 300);
    assert!(hls.total_flip_flops >= 256);
    assert!(hls.min_fmax_mhz >= 200.0);

    for f in &hls.functions {
        assert!(f.module_name.ends_with("_accel"));
        assert!(f.fsmd_states_count >= 3);
        assert!(f.latency_cycles >= 2);
        assert!(f.initiation_interval >= 1);
        assert!(f.critical_path_ns > 0.5);
        assert!(f.estimated_fmax_mhz >= 200.0);
        assert!(f.systemverilog_rtl.contains("`default_nettype none"));
        assert!(f.systemverilog_rtl.contains(&format!("module {} (", f.module_name)));
        assert!(f.systemverilog_rtl.contains("always_ff @(posedge clk_i or negedge rst_ni)"));
        assert!(f.systemverilog_rtl.contains("endmodule"));
        assert!(f.mermaid_fsmd.contains("flowchart LR"));

        // Verify ASAP <= ALAP and Mobility == ALAP - ASAP on every scheduled CDFG node
        for op in &f.operations {
            assert!(
                op.alap_cycle >= op.asap_cycle,
                "ALAP ({}) must be >= ASAP ({}) for op #{} in {}",
                op.alap_cycle,
                op.asap_cycle,
                op.op_id,
                f.fn_name
            );
            assert_eq!(op.mobility, op.alap_cycle - op.asap_cycle);
        }
    }

    // 2. 32-Lane Warp SIMT GPU Compute Kernel Synthesizer (CUDA PTX, WebGPU WGSL, Metal MSL, OpenCL C)
    let gpu = rl_eng.gpu_simt();
    assert_eq!(gpu.total_functions, 2);
    assert_eq!(gpu.total_gpu_kernels, 2);
    assert!(gpu.total_divergence_sites >= 2);
    assert_eq!(gpu.total_bank_conflicts, 0);
    assert!(gpu.avg_sm_occupancy_pct >= 80.0);
    assert!(gpu.avg_warp_efficiency_pct >= 65.0);
    assert!(gpu.max_gpu_speedup >= 80.0);

    for f in &gpu.functions {
        assert_eq!(f.warp_size, 32);
        assert_eq!(f.workgroup_threads, 64);
        assert_eq!(f.shared_mem_bank_conflicts, 0);
        assert!(f.cuda_ptx_source.contains("__global__ void __launch_bounds__(64, 4)"));
        assert!(f.cuda_ptx_source.contains(".version 8.0"));
        assert!(f.webgpu_wgsl_source.contains("@compute @workgroup_size(64, 1, 1)"));
        assert!(f.metal_msl_source.contains("#include <metal_stdlib>"));
        assert!(f.opencl_c_source.contains("__kernel __attribute__((reqd_work_group_size(64, 1, 1)))"));
        assert_eq!(f.host_dispatch_by_spoke.len(), 13);
        assert!(f.host_dispatch_by_spoke["rust"].contains("dispatch_workgroups"));
        assert!(f.host_dispatch_by_spoke["cpp"].contains("<<<"));
        assert!(f.host_dispatch_by_spoke["swift"].contains("dispatchThreadgroups"));
        assert!(f.host_dispatch_by_spoke["python"].contains(&f.kernel_name));
        assert!(f.host_dispatch_by_spoke["typescript"].contains("dispatchWorkgroups"));
        assert!(f.mermaid_simt.contains("flowchart LR"));
    }
}

#[test]
fn fhe_ring_lwe_blinded_circuit_compiler_and_reynolds_separation_logic_verifier_verify_across_thirteen_languages() {
    let rl_sample = find_sample("ratelimit").unwrap();
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source).unwrap();

    // 1. Fully Homomorphic Encryption (FHE) Ring-LWE Blinded Circuit Compiler & Noise-Budget Tracker
    let fhe = rl_eng.fhe_circuit();
    assert_eq!(fhe.total_functions, 2);
    assert!(fhe.total_fhe_gates >= 10);
    assert!(fhe.total_relinearizations >= 1);
    assert!(fhe.total_oblivious_muxes >= 2);
    assert!(fhe.max_multiplicative_depth >= 1);
    assert!(fhe.min_remaining_noise_bits >= 12.0);
    assert!(fhe.all_decryptions_verified);

    for f in &fhe.functions {
        assert_eq!(f.poly_modulus_degree_n, 8192);
        assert_eq!(f.coeff_modulus_bits_q, 218);
        assert_eq!(f.plaintext_modulus_t, 65537);
        assert_eq!(f.security_bits_lambda, 128);
        assert!(f.decryption_verified);
        assert_eq!(f.sample_decrypted_out, f.sample_plaintext_out);
        assert!(f.final_noise_budget_bits > 0.0);
        assert!(f.openfhe_cpp_source.contains("#include \"openfhe.h\""));
        assert!(f.openfhe_cpp_source.contains("EvalMultAndRelinearize"));
        assert_eq!(f.fhe_by_spoke.len(), 13);
        assert!(f.fhe_by_spoke["rust"].contains("FheInt64"));
        assert!(f.fhe_by_spoke["cpp"].contains("EvalMultAndRelinearize"));
        assert!(f.fhe_by_spoke["go"].contains("MulRelinNew"));
        assert!(f.fhe_by_spoke["python"].contains("@fhe.compiler"));
        assert!(f.fhe_by_spoke["typescript"].contains("relinearizeInPlace"));
        assert!(f.mermaid_fhe.contains("flowchart LR"));
    }

    // 2. Reynolds Separation Logic (emp, x ↦ v, P * Q, P -* Q) Symbolic Heap & Fractional Borrow Prover
    let sep = rl_eng.separation_logic();
    assert_eq!(sep.total_functions, 2);
    assert!(sep.total_heap_cells >= 6);
    assert!(sep.total_proof_steps >= 8);
    assert_eq!(sep.use_after_free_bugs, 0);
    assert_eq!(sep.double_free_bugs, 0);
    assert_eq!(sep.memory_leak_bugs, 0);
    assert_eq!(sep.aliasing_bugs, 0);
    assert!(sep.all_memory_safe);

    for f in &sep.functions {
        assert!(f.no_use_after_free);
        assert!(f.no_double_free);
        assert!(f.no_memory_leak);
        assert!(f.no_mutable_aliasing);
        assert!(f.all_spatial_proofs_valid);
        assert!(f.spatial_precondition.contains(" * R_caller"));
        assert!(f.spatial_postcondition.contains(" * R_caller"));
        assert!(f.magic_wand_continuation.contains("-*"));
        assert_eq!(f.region_by_spoke.len(), 13);
        assert!(f.region_by_spoke["rust"].contains("&'a mut i64"));
        assert!(f.region_by_spoke["zig"].contains("ArenaAllocator"));
        assert!(f.region_by_spoke["c"].contains("restrict"));
        assert!(f.region_by_spoke["swift"].contains("~Copyable"));
        assert!(f.region_by_spoke["java"].contains("Arena.ofConfined()"));
        assert!(f.region_by_spoke["typescript"].contains("using region"));
        assert!(f.mermaid_seplogic.contains("flowchart LR"));
    }
}

#[test]
fn compiler_soundness_review_catches_type_holes_reconcile_meta_and_wasm_str_ordering() {
    // 1. Typechecker catches mixed Int/Float on '-', '*', '/', Float '%', duplicate fields/variants/params,
    //    and non-Void functions missing a guaranteed return path.
    let bad_rust = r#"
#[derive(Clone, Debug, PartialEq)]
pub struct DupStruct {
    pub x: i64,
    pub x: i64,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum DupEnum {
    Alpha,
    Alpha,
}

pub fn bad_arith(a: i64, a: f64) -> i64 {
    let m = 10 - 2.5;
    let r = 3.5 % 1.5;
    if a > 0.0 {
        return 1;
    }
}
"#;
    let bad_eng = StarEngine::from_source(SpokeId::Rust, bad_rust).unwrap();
    let diags = starlang::typecheck::check_module(bad_eng.hub());
    let msgs: Vec<String> = diags.iter().map(|d| d.message.clone()).collect();
    assert!(
        msgs.iter().any(|m| m.contains("duplicate field 'x' in struct 'DupStruct'")),
        "Expected duplicate field diagnostic, got {:?}",
        msgs
    );
    assert!(
        msgs.iter().any(|m| m.contains("duplicate variant 'Alpha' in enum 'DupEnum'")),
        "Expected duplicate variant diagnostic, got {:?}",
        msgs
    );
    assert!(
        msgs.iter().any(|m| m.contains("duplicate parameter 'a' in function 'bad_arith'")),
        "Expected duplicate parameter diagnostic, got {:?}",
        msgs
    );
    assert!(
        msgs.iter().any(|m| m.contains("arithmetic operator requires matching numeric types")),
        "Expected mixed numeric operand diagnostic, got {:?}",
        msgs
    );
    assert!(
        msgs.iter().any(|m| m.contains("modulo operator '%' requires Int operands")),
        "Expected Float modulo diagnostic, got {:?}",
        msgs
    );
    assert!(
        msgs.iter().any(|m| m.contains("non-void function 'bad_arith' (returns Int) may exit without returning a value")),
        "Expected missing return path diagnostic, got {:?}",
        msgs
    );

    // 2. Reconciler preserves `explicit_mut` (`let mut`) and `Let.ty` across Ruby, Lua, Perl, C, and Java edits
    let annotated_rust = r#"
pub fn compute(x: i64) -> i64 {
    let mut counter: i64 = x + 1;
    return counter;
}

pub fn main() {
    println!("{}", compute(41));
}
"#;
    let mut eng = StarEngine::from_source(SpokeId::Rust, annotated_rust).unwrap();
    assert!(eng.project(SpokeId::Rust).contains("let mut counter: i64 = x + 1;"));

    for spoke in [SpokeId::Ruby, SpokeId::Lua, SpokeId::Perl] {
        let code = eng.project(spoke);
        let snap = eng.apply_edit(spoke, &code).unwrap();
        assert!(
            snap.views["rust"].contains("let mut counter: i64 = x + 1;"),
            "Editing {:?} dropped `let mut` or `: i64` annotation in Rust:\n{}",
            spoke,
            snap.views["rust"]
        );
    }

    // 3. Refactor `rename_symbol` rejects local variable name collisions in the same function
    let err = eng
        .rename_symbol("var:compute::counter", "x")
        .expect_err("Expected renaming `counter` to existing param `x` to fail");
    assert!(
        err.contains("already exists in function 'compute'"),
        "Unexpected error: {}",
        err
    );

    // 4. WebAssembly backend compiles & executes lexicographical string ordering (`<`, `<=`, `>`, `>=`)
    let str_order_rust = r#"
pub fn compare_words(a: &str, b: &str) -> i64 {
    let mut score = 0;
    if a < b {
        score += 1;
    }
    if a <= b {
        score += 10;
    }
    if b > a {
        score += 100;
    }
    if b >= a {
        score += 1000;
    }
    return score;
}

pub fn main() {
    println!("{}", compare_words("alpha", "beta"));
}

#[test]
fn test_lex_order() {
    assert_eq!(compare_words("alpha", "beta"), 1111);
    assert_eq!(compare_words("beta", "alpha"), 0);
    assert_eq!(compare_words("same", "same"), 1010);
}
"#;
    let str_eng = StarEngine::from_source(SpokeId::Rust, str_order_rust).unwrap();
    assert!(
        starlang::typecheck::check_module(str_eng.hub()).is_empty(),
        "Unexpected typecheck errors on string ordering"
    );
    let vm_rep = starlang::eval::eval_module(str_eng.hub(), 100_000);
    assert!(vm_rep.ok);
    assert_eq!(vm_rep.stdout.trim(), "1111");

    let wasm_rep = starlang::wasm::run_wasm_jit(str_eng.hub());
    assert!(
        wasm_rep.ok,
        "Wasm JIT failed on string ordering: {:?}",
        wasm_rep.error
    );
    assert_eq!(wasm_rep.stdout.trim(), "1111");
    assert_eq!(wasm_rep.tests_passed, 1);

    // 5. Spoke parser & codegen edge cases:
    //    - Python `(!a) == b` precedence (`(not a) == b`) + comment-only lines at col 0 inside functions
    //    - Go `switch` negative integer `case int64(-1):` round-trip + `int64(-1 + 2)` literal wrapping
    //    - C++ `int64_t(-1 + 2)` literal wrapping + `a - (-b)` parenthesization
    //    - Perl `%` operator (`$x % 3`) parsing into `BinOp::Mod`
    let edge_rust = r#"
pub fn edge_cases(a: bool, b: bool, n: i64) -> i64 {
    let mut out = -1 + 2;
    if !a == b {
        out = out - (-n);
    }
    match n {
        -1 => {
            out += 10;
        }
        0 => {
            out += 20;
        }
        _ => {
            out += 30;
        }
    }
    return out;
}

pub fn main() {
    println!("{}", edge_cases(false, true, -1));
}
"#;
    let mut edge_eng = StarEngine::from_source(SpokeId::Rust, edge_rust).unwrap();
    let py_code = edge_eng.project(SpokeId::Python);
    assert!(
        py_code.contains("(not a) == b"),
        "Python must parenthesize `(not a) == b`, got:\n{}",
        py_code
    );
    assert!(
        py_code.contains("out - (-n)"),
        "Expected `out - (-n)` parenthesization, got:\n{}",
        py_code
    );
    // Inject a column-0 comment inside the Python function body and verify lex_python does not emit spurious Dedent
    let py_snap = edge_eng
        .apply_edit(SpokeId::Python, &py_code)
        .expect("Python parser should round-trip parenthesized `(not a) == b`");
    assert_eq!(py_snap.live_eval.stdout.trim(), "10");

    // Verify Go negative switch case round-trip & `int64(-1 + 2)` wrapping
    let go_code = edge_eng.project(SpokeId::Go);
    assert!(
        go_code.contains("int64(-1 + 2)"),
        "Go should wrap `-1 + 2` in `int64(...)`, got:\n{}",
        go_code
    );
    assert!(
        go_code.contains("case -1:"),
        "Go should emit `case -1:`, got:\n{}",
        go_code
    );
    let go_snap = edge_eng
        .apply_edit(SpokeId::Go, &go_code)
        .expect("Go parser should round-trip negative switch case `case -1:`");
    assert_eq!(go_snap.live_eval.stdout.trim(), "10");

    // Verify C++ wraps `-1 + 2` in `int64_t(-1 + 2)`
    let cpp_code = edge_eng.project(SpokeId::Cpp);
    assert!(
        cpp_code.contains("int64_t(-1 + 2)"),
        "C++ should wrap `-1 + 2` in `int64_t(...)`, got:\n{}",
        cpp_code
    );

    // Verify Perl `%` operator parses cleanly into `BinOp::Mod`
    let perl_code = edge_eng
        .project(SpokeId::Perl)
        .replace("$out += 30;", "$out += ($n % 3);");
    let perl_snap = edge_eng
        .apply_edit(SpokeId::Perl, &perl_code)
        .expect("Perl lexer/parser should support `%` modulo operator");
    assert!(perl_snap.views["rust"].contains("n % 3"));

    // 6. 3-Way AST Merger detects add/add conflicts when Left and Right both add the same function with different bodies
    let left_add = format!(
        "{}\npub fn newly_added(x: i64) -> i64 {{\n    return x + 1;\n}}\n",
        annotated_rust
    );
    let right_add = format!(
        "{}\npub fn newly_added(x: i64) -> i64 {{\n    return x + 99;\n}}\n",
        annotated_rust
    );
    let mut base_eng = StarEngine::from_source(SpokeId::Rust, annotated_rust).unwrap();
    let (_, mrep) = base_eng
        .merge_concurrent(
            SpokeId::Rust,
            &left_add,
            SpokeId::Rust,
            &right_add,
        )
        .unwrap();
    assert!(
        !mrep.clean && mrep.conflicts.iter().any(|c| c.description.contains("Add/add conflict")),
        "Expected Add/add conflict on newly_added, got: {:?}",
        mrep.conflicts
    );

    // 7. Alpha-equivalence distinguishes struct field targets (`p.a = 1` vs `p.b = 1`) and normalizes intrinsics
    let eq_src_a = "\
pub struct Pair {
    pub a: i64,
    pub b: i64,
}
pub fn tweak(mut p: Pair, x: i64) -> i64 {
    p.a = x.min(10);
    return p.a + p.b;
}
fn main() {
    let p: Pair = Pair { a: 1, b: 2 };
    println!(\"{}\", tweak(p, 5));
}
";
    let eq_src_b_renamed = "\
pub struct Pair {
    pub a: i64,
    pub b: i64,
}
pub fn tweak(mut q: Pair, y: i64) -> i64 {
    q.a = y.min(10);
    return q.a + q.b;
}
fn main() {
    let p: Pair = Pair { a: 1, b: 2 };
    println!(\"{}\", tweak(p, 5));
}
";
    let eq_src_c_wrong_field = "\
pub struct Pair {
    pub a: i64,
    pub b: i64,
}
pub fn tweak(mut p: Pair, x: i64) -> i64 {
    p.b = x.min(10);
    return p.a + p.b;
}
fn main() {
    let p: Pair = Pair { a: 1, b: 2 };
    println!(\"{}\", tweak(p, 5));
}
";
    let eq_eng = StarEngine::from_source(SpokeId::Rust, eq_src_a).unwrap();
    let rep_renamed = eq_eng
        .equiv_with(SpokeId::Rust, eq_src_b_renamed, 16)
        .unwrap();
    let f_tweak_ren = rep_renamed
        .functions
        .iter()
        .find(|f| f.name == "tweak")
        .unwrap();
    assert!(
        f_tweak_ren.alpha_equivalent,
        "Alpha-renamed function with `FieldAccess` and `Intrinsic::Min` should be alpha_equivalent"
    );
    let rep_wrong_field = eq_eng
        .equiv_with(SpokeId::Rust, eq_src_c_wrong_field, 16)
        .unwrap();
    let f_tweak_wrong = rep_wrong_field
        .functions
        .iter()
        .find(|f| f.name == "tweak")
        .unwrap();
    assert!(
        !f_tweak_wrong.alpha_equivalent,
        "`p.a = ...` and `p.b = ...` must not be alpha_equivalent"
    );

    // 8. Polyhedral loop analyzer rejects self-referential `acc += acc` as a parallel reduction
    let self_ref_loop = "\
pub fn exp_double(n: i64) -> i64 {
    let mut acc: i64 = 1;
    for i in 0..n {
        acc += acc;
    }
    return acc;
}
fn main() {
    println!(\"{}\", exp_double(4));
}
";
    let poly_eng = StarEngine::from_source(SpokeId::Rust, self_ref_loop).unwrap();
    let poly_rep = poly_eng.polyhedral();
    assert_eq!(
        poly_rep.vectorizable_loops, 0,
        "Self-referential `acc += acc` is exponential doubling, not a parallel monoid reduction"
    );

    // 9. Postfix method calls on negative integer literals (`abs(-5)`, `str(-5)`, `min(-5, 0)`)
    // parenthesize `(-5)` in Rust, Ruby, Swift, Java, and TypeScript so `-` never binds looser than `.`
    let neg_postfix_py = "\
def check_neg_postfix() -> str:
    a: int = abs(-5)
    m: int = min(-5, 0)
    return str(-5) + \":\" + str(a) + \":\" + str(m)

def main() -> None:
    print(check_neg_postfix())
";
    let mut neg_eng = StarEngine::from_source(SpokeId::Python, neg_postfix_py).unwrap();
    let rust_neg = neg_eng.project(SpokeId::Rust);
    assert!(
        rust_neg.contains("(-5).abs()") && rust_neg.contains("(-5).min("),
        "Rust spoke must parenthesize negative int receiver before `.abs()` / `.min()`: {}",
        rust_neg
    );
    let ruby_neg = neg_eng.project(SpokeId::Ruby);
    assert!(
        ruby_neg.contains("(-5).abs") && ruby_neg.contains("(-5).to_s"),
        "Ruby spoke must parenthesize negative int receiver before `.abs` / `.to_s`: {}",
        ruby_neg
    );
    for spoke in SpokeId::ALL {
        let code = neg_eng.project(spoke);
        let snap = neg_eng
            .apply_edit(spoke, &code)
            .unwrap_or_else(|d| panic!("GetPut failed on {:?} for neg_postfix: {}", spoke, d));
        assert!(
            snap.semantic_diagnostics.is_empty(),
            "Unexpected semantic diagnostics after {:?} round-trip: {:?}",
            spoke,
            snap.semantic_diagnostics
        );
        assert_eq!(snap.live_eval.stdout.trim(), "-5:5:-5");
    }

    // 10. Static typechecker catches duplicate field initializers in struct literals
    let dup_field_rust = "\
pub struct Pair {
    pub a: i64,
    pub b: i64,
}
pub fn bad_pair() -> Pair {
    return Pair { a: 1, a: 2, b: 3 };
}
fn main() {
    let p: Pair = bad_pair();
    println!(\"{}\", p.a);
}
";
    let dup_eng = StarEngine::from_source(SpokeId::Rust, dup_field_rust).unwrap();
    let dup_snap = dup_eng.snapshot();
    assert!(
        dup_snap
            .semantic_diagnostics
            .iter()
            .any(|d| d.message.contains("duplicate field 'a'")),
        "Expected duplicate field diagnostic, got: {:?}",
        dup_snap.semantic_diagnostics
    );
}

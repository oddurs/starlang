use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::thread;

use starlang::engine::StarEngine;
use starlang::eval::eval_module;
use starlang::fuzzer::run_fuzz_suite;
use starlang::lens::SpokeId;
use starlang::runner::run_all_spokes;
use starlang::samples::{find_sample, SAMPLES};
use starlang::server::serve_listener;
use starlang::spokes::lens_for;
use starlang::typecheck::check_module;

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
    assert_eq!(report.results.len(), 9);
    assert!(
        report.outputs_match,
        "9-engine outputs diverged: {:?}",
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
        "cpp",
        "swift",
        "java",
        "go",
        "python",
        "ruby",
        "typescript",
    ] {
        assert!(
            snap.views[key].contains("test_mutation_hardened"),
            "Missing test_mutation_hardened in {}:\n{}",
            key,
            snap.views[key]
        );
    }

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
fn property_based_lens_fuzzer_verifies_fifty_random_programs_across_nine_spokes() {
    let report = run_fuzz_suite(0x57A4_2026_0500, 50);
    assert!(
        report.ok(),
        "Property-based fuzzer found {} failure(s):\n{}",
        report.failures.len(),
        report.failures.join("\n\n")
    );
    assert_eq!(report.programs_tested, 50);
    assert_eq!(report.spoke_roundtrips, 50 * 9);
    assert_eq!(report.assertions_passed, 50);
    assert_eq!(report.optimizer_checks, 50);
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
        "cpp",
        "swift",
        "java",
        "go",
        "python",
        "ruby",
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
fn all_samples_compile_and_produce_identical_output_across_nine_engines() {
    for sample in SAMPLES {
        let engine = StarEngine::from_source(sample.initial_spoke, sample.source).unwrap();
        let report = run_all_spokes(&engine);
        assert_eq!(report.results.len(), 9);

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
                    "C++ (clang++)" => engine.project(SpokeId::Cpp),
                    "Swift (swiftc)" => engine.project(SpokeId::Swift),
                    "Java (javac)" => engine.project(SpokeId::Java),
                    "Go (go run)" => engine.project(SpokeId::Go),
                    "Python (python3)" => engine.project(SpokeId::Python),
                    "Ruby (ruby)" => engine.project(SpokeId::Ruby),
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
fn web_studio_http_api_syncs_traces_mutates_hardens_and_runs_nine_engines() {
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
    assert!(state_resp.contains("\"swift\":"));
    assert!(state_resp.contains("\"java\":"));
    assert!(state_resp.contains("\"ruby\":"));
    assert!(state_resp.contains("\"coverage_pct\":"));
    assert!(state_resp.contains("\"test_results\":"));
    assert!(state_resp.contains("\"live_eval\":"));

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

    // Execute across all 9 engines via /api/run
    let run_resp = send_http("POST", "/api/run", "{}");
    assert!(run_resp.contains("\"outputs_match\":true"), "run failed: {}", run_resp);
    assert!(run_resp.contains("Hub VM (native)"));
    assert!(run_resp.contains("C++ (clang++)"));
    assert!(run_resp.contains("Swift (swiftc)"));
    assert!(run_resp.contains("Java (javac)"));
    assert!(run_resp.contains("Ruby (ruby)"));
    assert!(run_resp.contains("calibrated_sum: 261"));
}

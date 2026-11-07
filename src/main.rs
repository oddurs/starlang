use std::env;
use std::fs;
use std::path::Path;

use starlang::engine::StarEngine;
use starlang::eval::{eval_module_default, eval_tests_default};
use starlang::fuzzer::run_fuzz_suite;
use starlang::lens::SpokeId;
use starlang::merge::diff_sources;
use starlang::runner::run_all_spokes;
use starlang::samples::find_sample;
use starlang::server::serve_web_studio;
use starlang::verify::VerifyStatus;
use starlang::watcher::watch_directory;

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let cmd = args.first().map(|s| s.as_str()).unwrap_or("serve");

    match cmd {
        "serve" => {
            let port = parse_port(&args[1..]).unwrap_or(7878);
            if let Err(e) = serve_web_studio(port) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "watch" => {
            let dir = args.get(1).map(|s| s.as_str()).unwrap_or("./star_workspace");
            let stem = args.get(2).map(|s| s.as_str()).unwrap_or("program");
            if let Err(e) = watch_directory(Path::new(dir), stem) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "convert" => {
            if let Err(e) = run_convert(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "check" => {
            if let Err(e) = run_check(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "eval" => {
            if let Err(e) = run_eval_vm(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "test" => {
            if let Err(e) = run_tests_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "trace" => {
            if let Err(e) = run_trace_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "verify" => {
            if let Err(e) = run_verify_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "diff" => {
            if let Err(e) = run_diff_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "merge" => {
            if let Err(e) = run_merge_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "wasm" => {
            if let Err(e) = run_wasm_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "debug" => {
            if let Err(e) = run_debug_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "complexity" => {
            if let Err(e) = run_complexity_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "quickcheck" => {
            if let Err(e) = run_quickcheck_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "repair" => {
            if let Err(e) = run_repair_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "equiv" => {
            if let Err(e) = run_equiv_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "synth" => {
            if let Err(e) = run_synth_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "cfg" => {
            if let Err(e) = run_cfg_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "ssa" => {
            if let Err(e) = run_ssa_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "contracts" => {
            if let Err(e) = run_contracts_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "concolic" => {
            if let Err(e) = run_concolic_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "security" => {
            if let Err(e) = run_security_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "egraph" => {
            if let Err(e) = run_egraph_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "peval" => {
            if let Err(e) = run_peval_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "polyhedral" => {
            if let Err(e) = run_polyhedral_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "wcet" => {
            if let Err(e) = run_wcet_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "regalloc" => {
            if let Err(e) = run_regalloc_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "escape" => {
            if let Err(e) = run_escape_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "microarch" => {
            if let Err(e) = run_microarch_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "schedule" => {
            if let Err(e) = run_schedule_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "autodiff" => {
            if let Err(e) = run_autodiff_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "stability" => {
            if let Err(e) = run_stability_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "actors" => {
            if let Err(e) = run_actors_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "modelcheck" => {
            if let Err(e) = run_modelcheck_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "zk" => {
            if let Err(e) = run_zk_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "sql" => {
            if let Err(e) = run_sql_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "refinement" => {
            if let Err(e) = run_refinement_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "prob" => {
            if let Err(e) = run_prob_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "quantum" => {
            if let Err(e) = run_quantum_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "automata" => {
            if let Err(e) = run_automata_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "hls" => {
            if let Err(e) = run_hls_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "gpu" => {
            if let Err(e) = run_gpu_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "mutate" => {
            if let Err(e) = run_mutate_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "fuzz" => {
            if let Err(e) = run_fuzz_cli(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "refactor" => {
            if let Err(e) = run_refactor(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "optimize" => {
            if let Err(e) = run_optimize(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "run" => {
            if let Err(e) = run_file_all_compilers(&args[1..]) {
                eprintln!("Error: {}", e);
                std::process::exit(1);
            }
        }
        "demo" => {
            if let Err(e) = run_cli_demo() {
                eprintln!("Demo failed: {}", e);
                std::process::exit(1);
            }
        }
        "--help" | "-h" | "help" => {
            print_help();
        }
        other => {
            eprintln!("Unknown subcommand '{}'\n", other);
            print_help();
            std::process::exit(1);
        }
    }
}

fn parse_port(args: &[String]) -> Option<u16> {
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if arg == "--port" || arg == "-p" {
            return iter.next()?.parse().ok();
        }
        if let Ok(p) = arg.parse::<u16>() {
            return Some(p);
        }
    }
    None
}

fn load_engine_from_path(path_str: &str) -> Result<(StarEngine, SpokeId), String> {
    let path = Path::new(path_str);
    let ext = path
        .extension()
        .and_then(|e| e.to_str())
        .ok_or_else(|| format!("cannot infer language extension from '{}'", path_str))?;
    let spoke = SpokeId::from_name_or_ext(ext)
        .ok_or_else(|| format!("unsupported file extension '.{}'", ext))?;
    let src = fs::read_to_string(path)
        .map_err(|e| format!("failed reading '{}': {}", path.display(), e))?;
    let eng = StarEngine::from_source(spoke, &src).map_err(|d| d.to_string())?;
    Ok((eng, spoke))
}

fn parse_target_spoke(args: &[String]) -> Result<Option<SpokeId>, String> {
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--to" || args[i] == "-t" {
            let name = args
                .get(i + 1)
                .ok_or_else(|| "expected language name after --to".to_string())?;
            let spoke = SpokeId::from_name_or_ext(name)
                .ok_or_else(|| format!("unknown target spoke '{}'", name))?;
            return Ok(Some(spoke));
        }
        i += 1;
    }
    Ok(None)
}

fn run_convert(args: &[String]) -> Result<(), String> {
    let input = args.first().ok_or_else(|| {
        "usage: starlang convert <file> [--to rust|zig|c|cpp|swift|java|go|python|ruby|ts|star]"
            .to_string()
    })?;
    let (eng, src_spoke) = load_engine_from_path(input)?;

    let mut target = parse_target_spoke(&args[1..])?;
    if target.is_none() && args.len() == 2 {
        target = Some(
            SpokeId::from_name_or_ext(&args[1])
                .ok_or_else(|| format!("unknown target spoke '{}'", args[1]))?,
        );
    }

    if let Some(t) = target {
        print!("{}", eng.project(t));
    } else {
        for spoke in SpokeId::ALL {
            if spoke == src_spoke {
                continue;
            }
            println!("=== {} (.{}) ===", spoke.display_name(), spoke.extension());
            println!("{}", eng.project(spoke));
        }
    }
    Ok(())
}

fn run_check(args: &[String]) -> Result<(), String> {
    let input = args
        .first()
        .ok_or_else(|| "usage: starlang check <file>".to_string())?;
    let (eng, spoke) = load_engine_from_path(input)?;
    let diags = eng.validate();
    if diags.is_empty() {
        println!(
            "✓ {} ({} Hub semantic nodes): 0 static type/scope issues.",
            spoke.display_name(),
            eng.hub().node_count()
        );
        Ok(())
    } else {
        for d in &diags {
            eprintln!("{}", d);
        }
        Err(format!("{} semantic issue(s) found", diags.len()))
    }
}

fn run_eval_vm(args: &[String]) -> Result<(), String> {
    let input = args
        .first()
        .ok_or_else(|| "usage: starlang eval <file>".to_string())?;
    let (eng, _) = load_engine_from_path(input)?;
    let ev = eval_module_default(eng.hub());
    if ev.ok {
        print!("{}", ev.stdout);
        eprintln!("[Hub VM completed in {} AST steps]", ev.steps);
        Ok(())
    } else {
        Err(ev.error.unwrap_or_else(|| "Hub VM error".to_string()))
    }
}

fn run_tests_cli(args: &[String]) -> Result<(), String> {
    let input = args
        .first()
        .ok_or_else(|| "usage: starlang test <file>".to_string())?;
    let (eng, spoke) = load_engine_from_path(input)?;
    let diags = eng.validate();
    if !diags.is_empty() {
        for d in &diags {
            eprintln!("{}", d);
        }
        return Err(format!("{} semantic issue(s) found", diags.len()));
    }

    let results = eval_tests_default(eng.hub());
    if results.is_empty() {
        println!("0 unit tests found in {} ({})", input, spoke.display_name());
        return Ok(());
    }

    let mut failed = 0usize;
    for tr in &results {
        if tr.passed {
            println!("  ✓ test_{} ({} AST steps)", tr.name, tr.steps);
        } else {
            failed += 1;
            println!(
                "  ✗ test_{} ({} AST steps) — {}",
                tr.name,
                tr.steps,
                tr.error.as_deref().unwrap_or("failed")
            );
        }
    }
    println!(
        "\nTest result: {} ({}/{} passed via Hub VM from {})",
        if failed == 0 { "ok" } else { "FAILED" },
        results.len() - failed,
        results.len(),
        spoke.display_name()
    );
    if failed > 0 {
        Err(format!("{} unit test(s) failed", failed))
    } else {
        Ok(())
    }
}

fn run_trace_cli(args: &[String]) -> Result<(), String> {
    let (eng, label) = if let Some(path) = args.first() {
        let (e, spoke) = load_engine_from_path(path)?;
        (e, format!("{} ({})", path, spoke.display_name()))
    } else {
        let sample = find_sample("pipeline").ok_or("missing pipeline sample")?;
        let e =
            StarEngine::from_source(sample.initial_spoke, sample.source).map_err(|d| d.to_string())?;
        (e, format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()))
    };

    let rep = eng.trace();
    println!("=== Hub AST Coverage & Call-Graph Trace: {} ===", label);
    println!(
        "Coverage: {}% ({}/{} Hub AST statements executed across main + unit tests)",
        rep.coverage_pct, rep.covered_stmts, rep.total_stmts
    );

    println!("\nHotspots:");
    for h in &rep.hotspots {
        println!(
            "  • {:<22} {:>3} call(s) | {:>5} AST steps",
            format!("{}()", h.name),
            h.calls,
            h.total_steps
        );
    }

    println!("\nCall-Graph Trace:");
    for c in &rep.call_trace {
        let indent = "  ".repeat(c.depth.saturating_sub(1));
        println!(
            "  {}{}({}) => {} [{} steps]",
            indent, c.callee, c.args, c.result, c.steps
        );
    }

    if rep.uncovered.is_empty() {
        println!("\n✓ 0 uncovered AST statements.");
    } else {
        println!("\nUncovered AST Statements ({}):", rep.uncovered.len());
        for u in &rep.uncovered {
            println!("  ⚠ [node #{} in {}] {}", u.node_id, u.func, u.summary);
        }
    }

    if let Some(err) = rep.error {
        return Err(err);
    }
    Ok(())
}

fn run_verify_cli(args: &[String]) -> Result<(), String> {
    let (eng, label) = if let Some(path) = args.first() {
        let (e, spoke) = load_engine_from_path(path)?;
        (e, format!("{} ({})", path, spoke.display_name()))
    } else {
        let sample = find_sample("packets").ok_or("missing packets sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.verify();
    println!("=== Hub Symbolic Safety & Dead-Branch Verifier: {} ===", label);
    println!(
        "Safety Obligations: {}/{} proven safe | {} refuted | {} unproven | {} UNSAT dead branch(es) ({}ms)",
        rep.proven_safe,
        rep.total_obligations,
        rep.refuted,
        rep.warnings,
        rep.unreachable_branches.len(),
        rep.elapsed_ms
    );

    if !rep.obligations.is_empty() {
        println!("\nProof Obligations:");
        for ob in &rep.obligations {
            match &ob.status {
                VerifyStatus::ProvenSafe => {
                    println!(
                        "  ✓ [SAFE #{} in {}()] {}: {} — {}",
                        ob.id,
                        ob.func,
                        ob.kind.label(),
                        ob.expr_summary,
                        ob.proof_note
                    );
                }
                VerifyStatus::Refuted {
                    witness_call,
                    runtime_error,
                } => {
                    println!(
                        "  ✗ [REFUTED #{} in {}()] {}: {}\n      ↳ Counterexample witness: {} => {}",
                        ob.id,
                        ob.func,
                        ob.kind.label(),
                        ob.expr_summary,
                        witness_call,
                        runtime_error
                    );
                }
                VerifyStatus::UnprovenWarning => {
                    println!(
                        "  ⚠ [UNPROVEN #{} in {}()] {}: {} — {}",
                        ob.id,
                        ob.func,
                        ob.kind.label(),
                        ob.expr_summary,
                        ob.proof_note
                    );
                }
            }
        }
    }

    if rep.unreachable_branches.is_empty() {
        println!("\n✓ 0 UNSAT unreachable branches.");
    } else {
        println!("\nUNSAT Unreachable Branches ({}):", rep.unreachable_branches.len());
        for u in &rep.unreachable_branches {
            println!(
                "  ⚠ [stmt #{} in {}()] {}-branch of `{}` — {}",
                u.stmt_id, u.func, u.branch, u.cond_summary, u.reason
            );
        }
    }

    if rep.refuted > 0 {
        return Err(format!(
            "{} safety obligation(s) refuted with concrete crash counterexamples",
            rep.refuted
        ));
    }
    Ok(())
}

fn infer_spoke_and_read(path_str: &str) -> Result<(SpokeId, String), String> {
    let path = Path::new(path_str);
    let ext = path
        .extension()
        .and_then(|e| e.to_str())
        .ok_or_else(|| format!("cannot infer language extension from '{}'", path_str))?;
    let spoke = SpokeId::from_name_or_ext(ext)
        .ok_or_else(|| format!("unsupported file extension '.{}'", ext))?;
    let src = fs::read_to_string(path)
        .map_err(|e| format!("failed reading '{}': {}", path.display(), e))?;
    Ok((spoke, src))
}

fn run_diff_cli(args: &[String]) -> Result<(), String> {
    if args.len() < 2 {
        return Err("usage: starlang diff <left_file> <right_file>".to_string());
    }
    let (left_spoke, left_src) = infer_spoke_and_read(&args[0])?;
    let (right_spoke, right_src) = infer_spoke_and_read(&args[1])?;
    let rep = diff_sources(left_spoke, &left_src, right_spoke, &right_src)
        .map_err(|d| d.to_string())?;

    println!(
        "=== Cross-Language Hub AST Semantic Diff: {} ({}) <-> {} ({}) ===",
        args[0],
        left_spoke.display_name(),
        args[1],
        right_spoke.display_name()
    );
    if rep.identical {
        println!("✓ Semantically identical Hub ASTs (0 deltas).");
    } else {
        println!("Found {} semantic AST delta(s):", rep.deltas.len());
        for d in &rep.deltas {
            println!("  • [{:<8} in {}] {}", d.kind, d.scope, d.summary);
        }
    }
    Ok(())
}

fn run_merge_cli(args: &[String]) -> Result<(), String> {
    let positional: Vec<&str> = args
        .iter()
        .enumerate()
        .filter(|(idx, a)| {
            !a.starts_with('-')
                && (*idx == 0 || (args[*idx - 1] != "--to" && args[*idx - 1] != "-t"))
        })
        .map(|(_, a)| a.as_str())
        .collect();

    let out_target = parse_target_spoke(args)?;

    if positional.is_empty() {
        let sample = find_sample("alerts").ok_or("missing alerts sample")?;
        let mut eng = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;

        // Alice forks into Zig 0.16 and escalates `Severity.Critical` weight (5 -> 10) + adds `Fatal = 3`
        let base_zig = eng.project(SpokeId::Zig);
        let alice_zig = base_zig
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

        // Concurrently, Bob forks into Python off the SAME base Hub and updates `main()` window + adds a comment
        let base_py = eng.project(SpokeId::Python);
        let bob_py = base_py
            .replace(
                "        if ms < 0:\n            continue",
                "        # Skip negative jitter samples\n        if ms < 0:\n            continue",
            )
            .replace(
                "    samples = [80, -1, 240, 610, 520, 90]\n    report = evaluate_window(samples, 6)",
                "    samples = [80, -1, 1200, 240, 90]\n    report = evaluate_window(samples, 15)",
            );

        let (snap, rep) = eng
            .merge_concurrent(SpokeId::Zig, &alice_zig, SpokeId::Python, &bob_py)
            .map_err(|d| d.to_string())?;

        let passed = snap.test_results.iter().filter(|t| t.passed).count();
        if let Some(proj_spoke) = out_target {
            eprintln!(
                "✓ Clean 3-way merge ({} edits, 0 conflicts, {}/{} tests passed) -> projecting {}:",
                rep.applied_changes.len(),
                passed,
                snap.test_results.len(),
                proj_spoke.display_name()
            );
            print!("{}", eng.project(proj_spoke));
        } else {
            println!("=== 3-Way Concurrent Cross-Language Hub AST Merge Showcase (`alerts`) ===");
            println!(
                "Clean Merge: {} | Applied Edits: {} | Conflicts: {} | Hub Typecheck Issues: {}",
                rep.clean,
                rep.applied_changes.len(),
                rep.conflicts.len(),
                snap.semantic_diagnostics.len()
            );
            for ch in &rep.applied_changes {
                println!(
                    "  ✓ [{:<6} · {}] {}",
                    ch.spoke.display_name(),
                    ch.scope,
                    ch.summary
                );
            }
            println!(
                "Merged Hub VM stdout: {} | Unit Tests: {}/{} passed | Sidecar Metadata: {:?}\n",
                snap.live_eval.stdout.trim(),
                passed,
                snap.test_results.len(),
                snap.metadata_badges
            );
            println!("--- Unified Rust View (.rs) ---");
            print!("{}", eng.project(SpokeId::Rust));
        }

        if !rep.clean || !snap.semantic_diagnostics.is_empty() {
            return Err("built-in 3-way merge showcase failed".to_string());
        }
        return Ok(());
    }

    if positional.len() != 3 {
        return Err(
            "usage: starlang merge [<base_file> <left_file> <right_file>] [--to rust|zig|c|cpp|swift|java|go|python|ruby|ts|star]"
                .to_string(),
        );
    }

    let (mut base_eng, base_spoke) = load_engine_from_path(positional[0])?;
    let (left_spoke, left_src) = infer_spoke_and_read(positional[1])?;
    let (right_spoke, right_src) = infer_spoke_and_read(positional[2])?;

    let (snap, rep) = base_eng
        .merge_concurrent(left_spoke, &left_src, right_spoke, &right_src)
        .map_err(|d| d.to_string())?;

    eprintln!(
        "=== 3-Way Hub AST Merge: base={} ({}) | left={} ({}) | right={} ({}) ===",
        positional[0],
        base_spoke.display_name(),
        positional[1],
        left_spoke.display_name(),
        positional[2],
        right_spoke.display_name()
    );
    for ch in &rep.applied_changes {
        eprintln!(
            "  ✓ [{} · {}] {}",
            ch.spoke.display_name(),
            ch.scope,
            ch.summary
        );
    }

    if !rep.clean {
        for c in &rep.conflicts {
            eprintln!(
                "  ✗ CONFLICT [#{} in {}] {}\n      base:  {}\n      {}: {}\n      {}: {}",
                c.node_id,
                c.scope,
                c.description,
                c.base_summary,
                c.left_spoke.display_name(),
                c.left_summary,
                c.right_spoke.display_name(),
                c.right_summary
            );
        }
        return Err(format!("{} semantic merge conflict(s)", rep.conflicts.len()));
    }

    let proj_spoke = out_target.unwrap_or(base_spoke);
    if let Some(code) = snap.views.get(proj_spoke.as_str()) {
        print!("{}", code);
    }
    Ok(())
}

fn run_wasm_cli(args: &[String]) -> Result<(), String> {
    let mut file_path: Option<&str> = None;
    let mut emit_wat = false;
    let mut out_wasm: Option<&str> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--wat" | "-w" => {
                emit_wat = true;
                i += 1;
            }
            "--out" | "-o" => {
                let p = args
                    .get(i + 1)
                    .ok_or_else(|| "expected output path after --out".to_string())?;
                out_wasm = Some(p.as_str());
                i += 2;
            }
            other if !other.starts_with('-') && file_path.is_none() => {
                file_path = Some(other);
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }

    let (eng, label) = if let Some(p) = file_path {
        let (e, spoke) = load_engine_from_path(p)?;
        (e, format!("{} ({})", p, spoke.display_name()))
    } else {
        let sample = find_sample("backoff").ok_or("missing backoff sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let art = eng.compile_wasm()?;
    if let Some(out_path) = out_wasm {
        fs::write(out_path, &art.bytes)
            .map_err(|e| format!("failed writing '{}': {}", out_path, e))?;
    }

    if emit_wat {
        print!("{}", art.wat);
        return Ok(());
    }

    let rep = eng.run_wasm();
    println!("=== Hub -> WebAssembly 1.0 Binary (.wasm) & V8 JIT Runner: {} ===", label);
    println!(
        "Binary Size: {} bytes (Code: {}B, Data: {}B, Functions: {}) | Exports: {:?}",
        art.bytes.len(),
        art.code_bytes,
        art.data_bytes,
        art.func_count,
        art.exports
    );
    println!(
        "V8 Wasm JIT: ok={} ({}ms) | Unit Tests: {}/{} passed | stdout: {}",
        rep.ok,
        rep.duration_ms,
        rep.tests_passed,
        rep.tests_total,
        rep.stdout.trim()
    );
    if !rep.ok {
        return Err(rep
            .error
            .unwrap_or_else(|| "V8 Wasm execution failed".to_string()));
    }
    println!("\n--- Symbolic WebAssembly Text Disassembly (.wat) ---");
    print!("{}", art.wat);
    Ok(())
}

fn run_debug_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    let mut slice_target: Option<&str> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--slice" | "-s" => {
                let s = args
                    .get(i + 1)
                    .ok_or_else(|| "expected variable or step:N after --slice".to_string())?;
                slice_target = Some(s.as_str());
                i += 2;
            }
            other if !other.starts_with('-') && file_or_preset.is_none() => {
                file_or_preset = Some(other);
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.time_travel(slice_target);
    println!("=== Polyglot Time-Travel Debugger & 13-Spoke Line Mapper: {} ===", label);
    println!(
        "Recorded Steps: {} | Max Call Depth: {} | Status: {} | stdout: {}",
        rep.total_steps,
        rep.max_depth,
        if rep.ok { "OK" } else { "FAULT" },
        rep.final_stdout.trim()
    );

    println!("\nExecution Timeline (first 12 steps across 13 languages):");
    for st in rep.steps.iter().take(12) {
        let rs = st.spoke_lines.get("rust").copied().unwrap_or(0);
        let zig = st.spoke_lines.get("zig").copied().unwrap_or(0);
        let c = st.spoke_lines.get("c").copied().unwrap_or(0);
        let py = st.spoke_lines.get("python").copied().unwrap_or(0);
        let lua = st.spoke_lines.get("lua").copied().unwrap_or(0);
        let pl = st.spoke_lines.get("perl").copied().unwrap_or(0);
        println!(
            "  [Step {:>2}] {:<18} :: {:<34} | rs:L{:<3} zig:L{:<3} c:L{:<3} py:L{:<3} lua:L{:<3} pl:L{:<3}",
            st.step_index, st.func, st.summary, rs, zig, c, py, lua, pl
        );
    }

    if let Some(sl) = &rep.slice {
        println!(
            "\nDynamic Backward Causal Slice for '{}' (anchor=Step {}, {} causal steps):",
            sl.target,
            sl.anchor_step,
            sl.slice_steps.len()
        );
        for line in &sl.explanation {
            println!("  <- {}", line);
        }
    }

    if let Some(err) = rep.fault {
        return Err(err);
    }
    Ok(())
}

fn run_complexity_cli(args: &[String]) -> Result<(), String> {
    let (eng, label) = if let Some(p) = args.first() {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.complexity();
    println!("=== Polyglot Asymptotic Big-O, Gas Profiler & 13-Spoke Code Density: {} ===", label);
    println!(
        "Dominant Big-O: {} | Max Cyclomatic: {} | Max Loop Depth: {} | Wasm Binary: {} B",
        rep.dominant_big_o, rep.max_cyclomatic, rep.max_loop_depth, rep.wasm_bytes
    );
    println!(
        "Module Execution Gas: {} total (compute: {}, memory: {}, alloc: {}, branch: {} across {} VM steps)\n",
        rep.module_gas.total_gas,
        rep.module_gas.compute_gas,
        rep.module_gas.memory_gas,
        rep.module_gas.alloc_gas,
        rep.module_gas.branch_gas,
        rep.module_gas.total_steps
    );

    println!("Per-Function Complexity & Empirical Scaling (N = 4, 8, 16, 32, 64):");
    for f in &rep.functions {
        let curve: Vec<String> = f
            .scaling_points
            .iter()
            .map(|p| format!("N={}->{}g", p.n, p.total_gas))
            .collect();
        println!(
            "  • {:<54} | Static: {:<6} | Empirical: {:<6} ({:.2}x/2N) | Cyc: {:>2} | Depth: {} | {}",
            f.signature,
            f.static_big_o,
            f.empirical_big_o,
            f.growth_ratio,
            f.cyclomatic_complexity,
            f.max_loop_depth,
            curve.join(", ")
        );
    }

    println!("\n13-Spoke Code-Size & Token Density Matrix:");
    for m in &rep.spoke_metrics {
        println!(
            "  • {:<11} ({:<10}): {:>3} logic lines ({:>3} total) | {:>4} tokens | {:>5} bytes",
            m.display_name, m.spoke, m.logic_lines, m.total_lines, m.tokens, m.bytes
        );
    }
    Ok(())
}

fn run_quickcheck_cli(args: &[String]) -> Result<(), String> {
    let mut target_arg: Option<&str> = None;
    let mut trials: Option<usize> = None;
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--trials" || args[i] == "-n" {
            if let Some(val) = args.get(i + 1).and_then(|s| s.parse::<usize>().ok()) {
                trials = Some(val);
            }
            i += 2;
        } else if !args[i].starts_with('-') && target_arg.is_none() {
            target_arg = Some(args[i].as_str());
            i += 1;
        } else {
            i += 1;
        }
    }

    let (eng, label) = if let Some(p) = target_arg {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.quickcheck(trials);
    println!("=== Polyglot Property-Based QuickCheck, Invariant Synthesizer & Shrinker: {} ===", label);
    println!(
        "Functions: {} | Trials: {} ({}/fn) | Optimizer Equivalence Checks: {} | Invariants: {} | Status: {} ({}ms)\n",
        rep.total_functions,
        rep.total_trials,
        rep.trials_per_fn,
        rep.optimizer_checks,
        rep.total_invariants,
        if rep.all_passed { "ALL PASSED" } else { "COUNTEREXAMPLE FOUND" },
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "  • {} — {}/{} passed | Opt-Eq: {} | Deterministic: {}",
            f.signature,
            f.passed_trials,
            f.trials_run,
            f.optimizer_equivalent,
            f.deterministic
        );
        for inv in &f.discovered_invariants {
            println!("      ✓ Invariant: {}", inv);
        }
        if let Some(ce) = &f.counterexample {
            println!(
                "      ✗ Shrunk Counterexample ({} shrink steps): {} -> {} => {}",
                ce.shrink_steps, ce.original_args, ce.minimized_args, ce.fault
            );
            for (sp, line) in &ce.repro_by_spoke {
                println!("          [{:<10}] {}", sp, line);
            }
        }
    }

    if !rep.all_passed {
        return Err("QuickCheck found a property violation or crash counterexample".to_string());
    }
    Ok(())
}

fn run_repair_cli(args: &[String]) -> Result<(), String> {
    let mut target_arg: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && target_arg.is_none() {
            target_arg = Some(a.as_str());
        }
    }

    let (mut eng, label) = if let Some(p) = target_arg {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let (_, rep, injected) = eng.repair(true);
    println!("=== Counterexample-Guided Automated Program Repair (CEGIS): {} ===", label);
    if let Some(inj) = &injected {
        println!("Injected Demo Fault: {}", inj);
    }
    println!(
        "Status: {} | Candidates Evaluated: {} | Tests: {}/{} -> {}/{} | Safety Refuted: {} -> {} | QuickCheck: {} ({}ms)\n",
        if rep.repaired { "VERIFIED PATCH SYNTHESIZED" } else { "UNRESOLVED" },
        rep.candidates_evaluated,
        rep.tests_passed_before,
        rep.tests_total,
        rep.tests_passed_after,
        rep.tests_total,
        rep.safety_refuted_before,
        rep.safety_refuted_after,
        if rep.quickcheck_passed { "OK" } else { "FAIL" },
        rep.elapsed_ms
    );

    if !rep.faults.is_empty() {
        println!("Localized Faults via Time-Travel Backward Slice:");
        for f in &rep.faults {
            println!("  • [stmt #{} in {}()] {}", f.stmt_id, f.func, f.symptom);
        }
        println!();
    }

    if let Some(p) = &rep.patch {
        println!(
            "Synthesized Patch: [{}] in {}() (stmt #{}) :: {} -> {}",
            p.kind, p.func, p.stmt_id, p.before_summary, p.after_summary
        );
        for spoke_key in ["rust", "zig", "c", "python", "lua", "perl"] {
            if let Some(diff) = p.diffs_by_spoke.get(spoke_key) {
                if !diff.trim().is_empty() {
                    println!("  [{}]\n    {}", spoke_key, diff.replace('\n', "\n    "));
                }
            }
        }
    }

    if !rep.repaired {
        return Err("could not synthesize a 4-gate verified repair patch".to_string());
    }
    Ok(())
}

fn run_equiv_cli(args: &[String]) -> Result<(), String> {
    if args.len() < 2 {
        return Err("usage: starlang equiv <left_file> <right_file>".to_string());
    }
    let (left_eng, left_spoke) = load_engine_from_path(&args[0])?;
    let (right_spoke, right_src) = infer_spoke_and_read(&args[1])?;
    let rep = left_eng
        .equiv_with(right_spoke, &right_src, 32)
        .map_err(|d| d.to_string())?;

    println!(
        "=== Polyglot α-Equivalence & Bisimulation Verifier: {} ({}) <-> {} ({}) ===",
        args[0],
        left_spoke.display_name(),
        args[1],
        right_spoke.display_name()
    );
    println!(
        "Shared Functions: {} | De Bruijn α-Identical: {} | Bisimulation Trials: {} | Equivalent: {} ({}ms)",
        rep.shared_functions,
        rep.alpha_identical_count,
        rep.total_trials,
        rep.all_equivalent,
        rep.elapsed_ms
    );
    for f in &rep.functions {
        println!(
            "  • {} — α-identical: {} | bisimulation ({} trials): {}",
            f.signature, f.alpha_equivalent, f.bisimulation_trials, f.equivalent
        );
        if let Some(ce) = &f.distinguishing_counterexample {
            println!(
                "      ✗ Distinguishing Input ({} shrink steps): {} => {}",
                ce.shrink_steps, ce.minimized_args, ce.fault
            );
        }
    }
    if !rep.all_equivalent {
        return Err("modules are not behaviorally equivalent".to_string());
    }
    Ok(())
}

fn run_synth_cli(args: &[String]) -> Result<(), String> {
    let spec_arg = if args.is_empty() {
        None
    } else {
        Some(args.join(" "))
    };
    let sample = find_sample("scores").ok_or("missing scores sample")?;
    let mut eng = StarEngine::from_source(sample.initial_spoke, sample.source)
        .map_err(|d| d.to_string())?;
    let (rep, _) = eng.synthesize(spec_arg.as_deref(), false)?;

    println!(
        "=== Programming-by-Example (PBE) Observational-Equivalence Synthesizer: {} ===",
        rep.signature
    );
    println!(
        "Status: {} | I/O Examples: {} | Explored: {} ({} pruned by obs-equiv) | Unit Test: {} | Safety Proven: {} ({}ms)",
        if rep.ok {
            "VERIFIED AST SYNTHESIZED"
        } else {
            "UNRESOLVED"
        },
        rep.examples_count,
        rep.candidates_explored,
        rep.pruned_by_obs_equiv,
        rep.tests_passed,
        rep.safety_proven,
        rep.elapsed_ms
    );
    println!("Synthesized Hub AST Form:\n{}\n", rep.program_summary);

    for spoke_key in ["rust", "zig", "c", "python", "lua", "perl", "typescript", "star"] {
        if let Some(code) = rep.views_by_spoke.get(spoke_key) {
            println!("--- Projected {} ---\n{}", spoke_key, code);
        }
    }

    if !rep.ok || !rep.tests_passed {
        return Err("PBE synthesis failed to produce a verified program".to_string());
    }
    Ok(())
}

fn run_cfg_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    let mut emit_dot = false;
    for a in args {
        if a == "--dot" {
            emit_dot = true;
        } else if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.cfg();
    println!(
        "=== Polyglot Control-Flow Graph (CFG), Dominator Tree & Natural-Loop Analyzer: {} ===",
        label
    );
    println!(
        "Total Basic Blocks: {} | Total CFG Edges: {} | Natural Loops Detected: {}\n",
        rep.total_blocks, rep.total_edges, rep.total_natural_loops
    );

    for f in &rep.functions {
        println!(
            "Function: {} — {} basic block(s), {} natural loop(s), back-edges: {:?}",
            f.signature,
            f.blocks.len(),
            f.natural_loops,
            f.back_edges
        );
        for b in &f.blocks {
            println!(
                "  [BB{} · {:<10}] preds={:?} succs={:?} dom={:?} :: kind={}",
                b.id, b.label, b.predecessors, b.successors, b.dominators, b.kind
            );
        }
        if emit_dot {
            println!("  --- Graphviz DOT ---\n{}", f.dot);
        } else {
            println!("  --- Mermaid CFG ---\n{}", f.mermaid);
        }
    }
    Ok(())
}

fn run_ssa_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.ssa();
    println!(
        "=== Cytron Static Single Assignment (SSA), Dominance Frontiers, φ-Nodes & Liveness: {} ===",
        label
    );
    println!(
        "Functions: {} | Basic Blocks: {} | φ-Nodes: {} | SSA Definitions: {} | Dead Stores: {} ({}ms)\n",
        rep.total_functions,
        rep.total_blocks,
        rep.total_phi_nodes,
        rep.total_ssa_defs,
        rep.total_dead_stores,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        print!("{}", f.ssa_listing);
        println!("  Def-Use Chains ({}):", f.def_use_chains.len());
        for c in &f.def_use_chains {
            println!(
                "    • {:<16} (BB{} · {:<9}) -> {} use(s){}",
                c.ssa_var,
                c.def_block,
                c.def_kind,
                c.uses.len(),
                if c.is_dead_store { " [DEAD STORE]" } else { "" }
            );
        }
        println!();
    }
    Ok(())
}

fn run_contracts_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.contracts();
    println!(
        "=== Polyglot Hoare-Logic Design-by-Contract & Weakest-Precondition (WP) Verifier: {} ===",
        label
    );
    println!(
        "Functions: {} | Requires: {} | Loop Invariants: {} | Ensures: {} | Verification Conditions: {}/{} proven ({}ms)\n",
        rep.total_functions,
        rep.total_requires,
        rep.total_invariants,
        rep.total_ensures,
        rep.proven_vcs,
        rep.total_vcs,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [VCs: {}/{} proven]",
            f.signature, f.vcs_proven, f.vcs_total
        );
        for r in &f.requires {
            println!("  requires:       {}", r);
        }
        for inv in &f.loop_invariants {
            println!("  loop_invariant: {}", inv);
        }
        for ens in &f.ensures {
            println!("  ensures:        {}", ens);
        }
        println!();
    }

    println!("Verification Conditions ({}):", rep.verification_conditions.len());
    for vc in &rep.verification_conditions {
        println!(
            "  {} [VC #{} · {} in {}()] {} :: {}",
            if vc.proven { "✓" } else { "✗" },
            vc.id,
            vc.kind,
            vc.fn_name,
            vc.wp_formula,
            vc.proof_note
        );
    }

    if !rep.all_verified {
        return Err("one or more Hoare Verification Conditions could not be proven".to_string());
    }
    Ok(())
}

fn run_concolic_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    let mut inject = false;
    for a in args {
        if a == "--inject" || a == "-i" {
            inject = true;
        } else if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (mut eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let (rep, _) = eng.concolic(inject);
    println!(
        "=== Whitebox Concolic Path Explorer, Boundary-Negation Solver & Test Synthesizer: {} ===",
        label
    );
    println!(
        "Functions: {} | Distinct Execution Paths: {} | Branch Coverage: {}% ({}/{} branches) | Synthesized Assertions: {} ({}ms)\n",
        rep.total_functions,
        rep.total_paths,
        rep.branch_coverage_pct,
        rep.covered_branches,
        rep.total_branches,
        rep.synthesized_assertions_count,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [{} distinct path(s), {}% branch coverage ({}/{})]",
            f.signature,
            f.paths_discovered,
            f.branch_coverage_pct,
            f.covered_branches,
            f.total_branches
        );
        for p in &f.paths {
            println!(
                "  • [Path #{} · {:>2} steps] {} => {}\n      Π: {}",
                p.path_id, p.steps, p.input_args, p.output_val, p.path_condition
            );
        }
        println!();
    }

    if rep.total_paths == 0 {
        return Err("concolic explorer discovered 0 execution paths".to_string());
    }
    Ok(())
}

fn run_security_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.security_flow();
    println!(
        "=== Denning Lattice Information-Flow Taint, Sanitizer & Constant-Time Auditor: {} ===",
        label
    );
    println!(
        "Functions: {} | Sensitive Sinks: {}/{} guarded ({} unsanitized) | Sanitizers: {} | Taint Flows: {} | All Sinks Safe: {} ({}ms)\n",
        rep.total_functions,
        rep.safe_sinks,
        rep.total_sinks,
        rep.unsanitized_sinks,
        rep.total_sanitizers,
        rep.total_flows,
        rep.all_sinks_safe,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Sanitizers: {} | Constant-Time: {}]",
            f.signature, f.sanitizers_applied, f.constant_time_clean
        );
        for fl in &f.flow_edges {
            println!(
                "  flow [{}]: {} -> {} ({})",
                fl.flow_kind, fl.from_var, fl.to_target, fl.taint_label
            );
        }
        for s in &f.sink_audits {
            println!(
                "  {} sink [{}]: {} ({}) — {}",
                if s.safe { "✓" } else { "✗" },
                s.sink_kind,
                s.expr_summary,
                s.taint_state,
                s.note
            );
        }
        println!("  timing: {}\n", f.timing_note);
    }

    if !rep.all_sinks_safe {
        return Err(format!(
            "{} sensitive sink(s) reached by unsanitized taint",
            rep.unsanitized_sinks
        ));
    }
    Ok(())
}

fn run_egraph_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    let mut apply = false;
    for a in args {
        if a == "--apply" || a == "-a" {
            apply = true;
        } else if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (mut eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("pipeline").ok_or("missing pipeline sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let (rep, _) = eng.egraph(apply);
    println!(
        "=== Equality Saturation & Congruence-Closure E-Graph Superoptimizer: {} ===",
        label
    );
    println!(
        "E-Classes: {} | E-Nodes: {} | Congruence Unions: {} ({} saturation iters) | Rewrites: {} | Dead Branches Pruned: {} | Gas: {} -> {} (saved {}) | Validated: {} ({}ms)\n",
        rep.total_eclasses,
        rep.total_enodes,
        rep.total_unions,
        rep.saturation_iterations,
        rep.expressions_optimized,
        rep.dead_branches_pruned,
        rep.cost_before,
        rep.cost_after,
        rep.gas_saved,
        rep.translation_validated,
        rep.elapsed_ms
    );

    if !rep.rules_fired.is_empty() {
        let rules_str: Vec<String> = rep
            .rules_fired
            .iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect();
        println!("Rewrite Rules Fired: {}", rules_str.join(", "));
    }

    for w in &rep.rewrites {
        println!(
            "  • [{} · E-Class #{} ({} forms)] cost {} -> {} :: {}  ==>  {}",
            w.scope,
            w.eclass_id,
            w.class_size,
            w.cost_before,
            w.cost_after,
            w.before_expr,
            w.after_expr
        );
    }

    if !rep.translation_validated {
        return Err("E-Graph superoptimizer translation validation failed".to_string());
    }
    Ok(())
}

fn run_peval_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    let mut apply = false;
    for a in args {
        if a == "--apply" || a == "-a" {
            apply = true;
        } else if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (mut eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let (rep, _) = eng.partial_eval(apply);
    println!(
        "=== Futamura Partial Evaluator, Interprocedural Specializer & Loop Unroller: {} ===",
        label
    );
    println!(
        "Specialized Calls: {} | Residual Fns: {} | Static Branches Folded: {} | Loops Unrolled: {} | E-Graph Rewrites: {} ({}ms)",
        rep.specialized_calls,
        rep.residual_functions_synthesized,
        rep.static_branches_folded,
        rep.loops_unrolled,
        rep.egraph_rewrites,
        rep.elapsed_ms
    );
    println!(
        "VM Steps: {} -> {} | Gas: {} -> {} | AST Nodes: {} -> {} | Translation Validated: {} ({}/{} tests pass)\n",
        rep.vm_steps_before,
        rep.vm_steps_after,
        rep.gas_before,
        rep.gas_after,
        rep.nodes_before,
        rep.nodes_after,
        rep.translation_validated,
        rep.tests_passed,
        rep.tests_total
    );

    for s in &rep.specializations {
        println!(
            "  • [{}() -> {}()] bindings: {} :: {}",
            s.caller, s.callee, s.static_bindings, s.summary
        );
    }

    if !rep.translation_validated {
        return Err("Futamura partial evaluator translation validation failed".to_string());
    }
    Ok(())
}

fn run_polyhedral_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("pipeline").ok_or("missing pipeline sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.polyhedral();
    println!(
        "=== Polyhedral Loop Dependence, Monoid Reduction & 13-Spoke SIMD Vectorizer: {} ===",
        label
    );
    println!(
        "Loops Analyzed: {} | SIMD Vectorizable: {} | Map-Reduce Parallelizable: {} | Sequential State Loops: {} | Reductions: {} | Max 4-Lane SIMD Speedup: {:.2}x ({}ms)\n",
        rep.total_loops,
        rep.vectorizable_loops,
        rep.map_reduce_loops,
        rep.sequential_state_loops,
        rep.total_reductions,
        rep.max_simd4_speedup,
        rep.elapsed_ms
    );

    for lp in &rep.loops {
        println!(
            "Loop #{} in {}() [{} · {}] :: SIMD={} ({:.2}x) | Brent T1/Tinf(64)={:.2}x",
            lp.loop_id,
            lp.fn_name,
            lp.loop_kind,
            lp.classification,
            lp.simd_vectorizable,
            lp.estimated_simd4_speedup,
            lp.brent_parallelism_n64
        );
        println!("  Domain:     {}", lp.iteration_domain);
        println!(
            "  Work/Span:  T1 = {} | Tinf = {}",
            lp.work_t1_symbolic, lp.span_tinf_symbolic
        );
        if !lp.reductions.is_empty() {
            println!("  Reductions: {}", lp.reductions.join(", "));
        }
        for d in &lp.dependences {
            println!(
                "  Dep [{} · dist {}]: {} — {}",
                d.kind, d.distance, d.variable, d.note
            );
        }
        for spk in ["rust", "zig", "c", "python", "perl"] {
            if let Some(code) = lp.vectorized_by_spoke.get(spk) {
                println!("  [{}]\n    {}", spk, code.replace('\n', "\n    "));
            }
        }
        println!();
    }

    if rep.total_loops == 0 {
        return Err("no loops found in module for polyhedral analysis".to_string());
    }
    Ok(())
}

fn run_wcet_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.termination_wcet();
    println!(
        "=== Floyd-Turing Well-Founded Ranking Termination Prover & IPET WCET Analyzer: {} ===",
        label
    );
    println!(
        "Functions: {} | Loops Audited: {} | Proven Terminating: {} | Diverging/Unproven: {} | Module BCET(N=64): {}c | Module WCET(N=64): {}c | All Terminating: {} ({}ms)\n",
        rep.total_functions,
        rep.total_loops_audited,
        rep.proven_terminating_loops,
        rep.diverging_or_unproven_loops,
        rep.module_bcet_cycles_n64,
        rep.module_wcet_cycles_n64,
        rep.all_terminating,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Terminating: {} | BCET: {} ({}c) | WCET: {} ({}c) | Jitter: {:.2}x]",
            f.signature,
            f.proven_terminating,
            f.bcet_symbolic,
            f.bcet_cycles_n64,
            f.wcet_symbolic,
            f.wcet_cycles_n64,
            f.jitter_ratio
        );
        for lp in &f.loop_proofs {
            println!(
                "  {} [{}] {}\n      Ranking V(σ):       {}\n      Bounded-Below VC:   {}\n      Strict-Decrease VC: {}\n      Note:               {}",
                if lp.proven_terminating { "✓" } else { "✗" },
                lp.loop_header,
                lp.status,
                lp.ranking_function,
                lp.bounded_below_vc,
                lp.strict_decrease_vc,
                lp.witness_or_note
            );
        }
        println!();
    }

    if !rep.all_terminating {
        return Err("one or more loops could not be proven terminating".to_string());
    }
    Ok(())
}

fn run_regalloc_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    let mut k_regs: Option<usize> = None;
    let mut i = 0;
    while i < args.len() {
        if args[i] == "-k" || args[i] == "--registers" {
            if let Some(val) = args.get(i + 1).and_then(|s| s.parse::<usize>().ok()) {
                k_regs = Some(val);
            }
            i += 2;
        } else if !args[i].starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(args[i].as_str());
            i += 1;
        } else {
            i += 1;
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.regalloc(k_regs);
    println!(
        "=== Chaitin-Briggs Kempe Graph-Coloring & Linear-Scan Register Allocator (K={}): {} ===",
        rep.k_registers, label
    );
    println!(
        "Functions: {} | Virtual Regs: {} | Interference Edges: {} | Max Pressure: {} | Coalesced Moves: {} | Spills: {} | AArch64 Insts: {} | x86_64 Insts: {} ({}ms)\n",
        rep.total_functions,
        rep.total_virtual_regs,
        rep.total_interference_edges,
        rep.max_register_pressure,
        rep.total_coalesced_moves,
        rep.total_spills,
        rep.total_aarch64_insts,
        rep.total_x86_64_insts,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Colors: {}/{} | Clique Pressure: {} | Coalesced: {} | Spills: {} | Frame: {}B]",
            f.signature,
            f.chromatic_colors_used,
            f.k_registers,
            f.max_pressure_clique,
            f.coalesced_moves,
            f.spilled_vars,
            f.stack_frame_bytes
        );
        for iv in &f.intervals {
            println!(
                "  • {:<12} [pc {:>2}..{:>2}] deg={:<2} wt={:<6.1} -> ARM64: {:<10} | x86_64: {:<18} | LinScan: {}",
                iv.var_name,
                iv.start_pc,
                iv.end_pc,
                iv.degree,
                iv.spill_weight,
                iv.aarch64_loc,
                iv.x86_64_loc,
                iv.linear_scan_loc
            );
        }
        println!("  --- AArch64 (ARM64 AAPCS64) Assembly ---\n{}", f.aarch64_asm);
        println!("  --- x86_64 (System V AMD64) Assembly ---\n{}", f.x86_64_asm);
    }

    if rep.total_virtual_regs == 0 {
        return Err("register allocator found 0 virtual registers".to_string());
    }
    Ok(())
}

fn run_escape_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("scores").ok_or("missing scores sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.escape_analysis();
    println!(
        "=== Interprocedural Escape Analysis, Scalar Replacement (SROA) & RVO Optimizer: {} ===",
        label
    );
    println!(
        "Functions: {} | Alloc Sites: {} | Stack/SROA Promoted: {} | RVO Return-Slot: {} | SROA Fields: {} | Heap Saved: {}B/run ({}% heap elision, {}ms)\n",
        rep.total_functions,
        rep.total_alloc_sites,
        rep.stack_promoted_sites,
        rep.rvo_eliminated_sites,
        rep.sroa_scalarized_fields,
        rep.total_bytes_saved_per_run,
        rep.heap_reduction_pct,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Sites: {} | Stack/SROA: {} | RVO: {} | Saved: {}B/call]",
            f.signature,
            f.total_sites,
            f.stack_or_sroa_sites,
            f.rvo_sites,
            f.bytes_saved_per_call
        );
        for s in &f.sites {
            println!(
                "  • [{} · {}] {}\n      Strategy: {} (saves ~{}B, SROA fields: {})\n      Note:     {}",
                s.kind,
                s.escape_state,
                s.expr_summary,
                s.promotion_strategy,
                s.estimated_bytes_saved,
                s.sroa_fields,
                s.note
            );
        }
        println!();
    }

    Ok(())
}

fn run_microarch_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.microarch();
    println!(
        "=== 4-Wide Out-of-Order Superscalar CPU, 2-Bit Branch Predictor & 8-Way L1D Cache Simulator: {} ===",
        label
    );
    println!(
        "Retired μops: {} | In-Order Cycles: {}c -> 4-Wide OoO ROB: {}c (IPC: {:.2}, {:.2}x OoO speedup) | Branch Acc: {:.1}% ({}/{} mispredicts, +{}c penalty) | L1D Cache Hit Rate: {:.1}% ({} hits, {} prefetch, {} misses, {}ms)\n",
        rep.total_uops_retired,
        rep.total_in_order_cycles,
        rep.total_ooo_cycles,
        rep.superscalar_ipc,
        rep.ooo_speedup,
        rep.branch_accuracy_pct,
        rep.branch_mispredictions,
        rep.total_branches,
        rep.branch_penalty_cycles,
        rep.l1d_hit_rate_pct,
        rep.l1d_hits,
        rep.l1d_prefetch_hits,
        rep.l1d_misses,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [μops: {} | In-Order: {}c -> OoO: {}c | IPC: {:.2} | Bottleneck: {}]",
            f.signature,
            f.uops_retired,
            f.in_order_cycles,
            f.ooo_cycles,
            f.superscalar_ipc,
            f.bottleneck
        );
    }
    println!();

    for b in &rep.branch_sites {
        println!(
            "  • Branch stmt#{} [{}]: ({}) -> Taken: {}, NotTaken: {}, Acc: {:.1}% ({} mispredicts, +{}c)",
            b.stmt_id,
            b.fn_name,
            b.branch_expr,
            b.taken_count,
            b.not_taken_count,
            b.accuracy_pct,
            b.mispredictions,
            b.penalty_cycles
        );
    }

    for c in &rep.cache_sites {
        println!(
            "  • L1D Cache {}: {} accesses -> {} L1 hits, {} prefetch hits, {} misses ({:.1}% hit rate, {}c)",
            c.site_label,
            c.accesses,
            c.l1_hits,
            c.prefetch_hits,
            c.misses,
            c.hit_rate_pct,
            c.memory_cycles
        );
    }

    if rep.total_uops_retired == 0 {
        return Err("microarchitectural simulator retired 0 uops".to_string());
    }
    Ok(())
}

fn run_schedule_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.schedule_instructions();
    println!(
        "=== Gibbons-Muchnick Critical-Path DAG List Instruction Scheduler: {} ===",
        label
    );
    println!(
        "Functions: {} | Instructions: {} | DAG Edges: {} | Cycles: {}c -> {}c | Stall Bubbles Eliminated: {} | Reordered Insts: {} | Speedup: {:.2}x ({}ms)\n",
        rep.total_functions,
        rep.total_instructions,
        rep.total_dag_edges,
        rep.total_cycles_before,
        rep.total_cycles_after,
        rep.total_bubbles_eliminated,
        rep.total_reordered_insts,
        rep.overall_speedup,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Insts: {} | DAG Edges: {} | Critical Path: {}c | {}c -> {}c (-{} stall bubbles, {:.2}x)]",
            f.signature,
            f.inst_count,
            f.dag_edges_count,
            f.critical_path_cycles,
            f.in_order_cycles_before,
            f.scheduled_cycles_after,
            f.bubbles_eliminated,
            f.speedup_ratio
        );
        println!("  --- Scheduled Pipeline Listing ---\n{}", f.scheduled_listing);
    }

    if rep.total_instructions == 0 {
        return Err("instruction scheduler found 0 instructions".to_string());
    }
    Ok(())
}

fn run_autodiff_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    let mut inject = false;
    for a in args {
        if a == "--inject" || a == "-i" {
            inject = true;
        } else if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (mut eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("pipeline").ok_or("missing pipeline sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let (rep, _) = eng.autodiff(inject);
    println!(
        "=== Forward-Mode Dual-Number & Reverse-Mode Wengert-Tape Automatic Differentiation: {} ===",
        label
    );
    println!(
        "Functions: {} ({} differentiable) | Verified Partials: {}/{} | Wengert Tape Nodes: {} | Max Lipschitz Bound L: {:.2} | Synthesized Gradient: `{}` ({}ms)\n",
        rep.total_functions,
        rep.differentiable_functions,
        rep.verified_partials,
        rep.total_partials,
        rep.total_tape_nodes,
        rep.max_lipschitz_bound,
        rep.synthesized_grad_fn_name,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Partials: {} | Tape Nodes: {} | Lipschitz L: {:.2} | Jacobian L1: {:.2}]",
            f.signature,
            f.differentiable_params,
            f.tape_nodes_count,
            f.lipschitz_bound,
            f.jacobian_norm_l1
        );
        for p in &f.partials {
            println!(
                "  • {} @ {} => Primal: {} | Forward Dual: {:.3} | Reverse Tape: {:.3} | Finite-Diff: {:.3} [{}]",
                p.symbolic_derivative,
                p.sample_point,
                p.primal_value,
                p.forward_dual_deriv,
                p.reverse_tape_adjoint,
                p.finite_diff_approx,
                if p.dual_matches_reverse { "✓ VERIFIED" } else { "⚠ MISMATCH" }
            );
        }
        println!();
    }

    if !rep.all_gradients_verified {
        return Err("one or more forward/reverse gradients did not match".to_string());
    }
    Ok(())
}

fn run_stability_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.numerical_stability();
    println!(
        "=== IEEE-754 / Fixed-Point Numerical Stability, Condition Number κ & Lipschitz Auditor: {} ===",
        label
    );
    println!(
        "Functions: {} | Max Condition κ: {:.2} | Max Lipschitz L: {:.2} | Quantization Sites: {} | Overflow Sites: {} | Cancellation Sites: {} ({}ms)\n",
        rep.total_functions,
        rep.max_condition_number,
        rep.max_lipschitz_constant,
        rep.quantization_sites,
        rep.overflow_sites,
        rep.cancellation_sites,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!("Function: {} [{}]", f.signature, f.stability_grade);
        for h in &f.hazards {
            println!(
                "  • [#{} · {} ({})] {}\n      Max Error: {:.2} bits/ULPs — {}",
                h.site_id,
                h.kind,
                h.severity,
                h.expr_summary,
                h.max_error_ulps_or_bits,
                h.recommendation
            );
        }
        println!();
    }

    if rep.total_functions == 0 {
        return Err("numerical stability auditor found 0 functions".to_string());
    }
    Ok(())
}

fn run_actors_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.actors();
    println!(
        "=== Lamport Vector-Clock Happens-Before (→) Race Detector, Deadlock Prover & 13-Spoke Actor Synthesizer: {} ===",
        label
    );
    println!(
        "Functions: {} | Actor Stages: {} | Vector-Clock Events: {} | Concurrent Races: {} | Deadlock Cycles: {} | Data-Race Free: {} ({}ms)\n",
        rep.total_functions,
        rep.total_actor_stages,
        rep.total_vc_events,
        rep.total_races_detected,
        rep.total_wait_for_cycles,
        rep.all_data_race_free,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [{} | Cap: {} | DRF: {} | Deadlock-Free: {}]",
            f.signature,
            f.topology_kind,
            f.channel_capacity,
            f.data_race_free,
            f.deadlock_free
        );
        for e in &f.events {
            println!(
                "  • e{} [{:<17} · {:<10}] VC={:?} {} — {}",
                e.event_id,
                e.actor_name,
                e.op_kind,
                e.vector_clock,
                e.variable,
                e.happens_before_note
            );
        }
        println!();
    }

    if !rep.all_data_race_free || !rep.all_deadlock_free {
        return Err("concurrency verifier detected a data race or deadlock cycle".to_string());
    }
    Ok(())
}

fn run_modelcheck_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.model_check();
    println!(
        "=== Explicit-State Bounded Model Checker (Kripke Structure), Temporal Safety (□I), Liveness (□◇) & TLA+ Synthesizer: {} ===",
        label
    );
    println!(
        "Functions: {} | Reachable States: {} | Transitions: {} | Verified Properties: {}/{} | All Verified: {} ({}ms)\n",
        rep.total_functions,
        rep.total_reachable_states,
        rep.total_transitions,
        rep.verified_properties,
        rep.total_properties,
        rep.all_verified,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [States: {} | Transitions: {} | Max Depth: {}]",
            f.signature, f.reachable_states, f.transitions_explored, f.max_bfs_depth
        );
        for p in &f.properties {
            println!(
                "  {} [{}] {} ({} states)\n      ↳ {}",
                if p.verified { "✓" } else { "✗" },
                p.kind,
                p.formula,
                p.states_checked,
                p.proof_or_counterexample
            );
        }
        println!("  --- Synthesized TLA+ Specification ---\n{}\n", f.tla_plus_spec);
    }

    if !rep.all_verified {
        return Err("one or more temporal or linearizability properties failed".to_string());
    }
    Ok(())
}

fn run_zk_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.zk_r1cs();
    println!(
        "=== Rank-1 Constraint System (R1CS) Arithmetic Circuit Compiler & ZK Witness Verifier: {} ===",
        label
    );
    println!(
        "Field: {} | Functions: {} | Wires: {} | Constraints: {}/{} satisfied | All Verified: {} ({}ms)\n",
        rep.field_modulus_str,
        rep.total_functions,
        rep.total_wires,
        rep.satisfied_constraints,
        rep.total_constraints,
        rep.all_circuits_satisfied,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Wires: {} | Constraints: {}/{} | Public Inputs: {} | Private Witnesses: {} | Depth: {}]",
            f.signature,
            f.total_wires,
            f.satisfied_constraints,
            f.r1cs_constraints,
            f.public_inputs,
            f.private_witnesses,
            f.multiplicative_depth
        );
        for c in f.constraints.iter().take(8) {
            println!(
                "  {} #{:<2} [{:<13}] ({}) * ({}) == ({}) [{}]",
                if c.satisfied { "✓" } else { "✗" },
                c.constraint_id,
                c.gate_kind,
                c.a_linear_comb,
                c.b_linear_comb,
                c.c_linear_comb,
                c.source_note
            );
        }
        println!("  --- Synthesized Circom 2.1.6 ZK Template ---\n{}\n", f.circom_template);
    }

    if !rep.all_circuits_satisfied {
        return Err("one or more R1CS constraints failed witness verification".to_string());
    }
    Ok(())
}

fn run_sql_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.relational_sql();
    println!(
        "=== Relational Algebra (σ, π, Γ), Selection Pushdown & Vectorized SQL Optimizer: {} ===",
        label
    );
    println!(
        "Functions: {} | Relational Queries Lifted: {} | Pushed Predicates: {} | Volcano: {}c -> Columnar: {}c ({:.2}x speedup, {}ms)\n",
        rep.total_functions,
        rep.query_lifted_functions,
        rep.total_pushed_predicates,
        rep.total_volcano_cycles,
        rep.total_columnar_cycles,
        rep.overall_columnar_speedup,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Volcano: {}c -> Columnar: {}c ({:.2}x)]",
            f.signature, f.volcano_tuple_cycles, f.vectorized_columnar_cycles, f.columnar_speedup
        );
        println!("  Relational Algebra: {}", f.relational_algebra_expr);
        println!("  --- Synthesized ANSI SQL Query ---\n{}\n", f.ansi_sql_query);
    }

    if rep.total_functions == 0 {
        return Err("relational SQL optimizer found 0 functions".to_string());
    }
    Ok(())
}

fn run_refinement_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.liquid_refinements();
    println!(
        "=== Liquid Refinement Types ({{ ν: T | φ(ν) }}) & Constrained Horn Clause (CHC) Prover: {} ===",
        label
    );
    println!(
        "Functions: {} | Refined Bindings: {} | Qualifiers: {} | CHCs Discharged: {}/{} | All Verified: {} ({}ms)\n",
        rep.total_functions,
        rep.total_refined_bindings,
        rep.total_qualifiers_inferred,
        rep.discharged_horn_clauses,
        rep.total_horn_clauses,
        rep.all_subtypes_verified,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Bindings: {} | CHCs: {}/{} | Fixpoint Iters: {}]",
            f.refined_signature,
            f.total_bindings,
            f.horn_clauses_discharged,
            f.horn_clauses_total,
            f.fixpoint_iterations
        );
        for b in &f.bindings {
            println!("  • [{:<13}] {:<16} :: {}", b.role, b.symbol, b.liquid_type);
        }
        for c in f.horn_clauses.iter().take(6) {
            println!(
                "  {} CHC #{:<2} [{:<22}] {} ({})",
                if c.discharged { "✓" } else { "✗" },
                c.clause_id,
                c.kind,
                c.horn_implication,
                c.solver_note
            );
        }
        println!("  --- SMT-LIB2 HORN Logic Script ---\n{}\n", f.smtlib2_horn_script);
    }

    if !rep.all_subtypes_verified {
        return Err("one or more Liquid Refinement Constrained Horn Clauses failed".to_string());
    }
    Ok(())
}

fn run_prob_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.probabilistic_entropy();
    println!(
        "=== Probabilistic MCMC Sampler & Quantitative Information Flow (QIF) Shannon Entropy Quantifier: {} ===",
        label
    );
    println!(
        "Functions: {} | MCMC Samples: {} | Max Output Entropy H(Y): {:.2} bits | Max Mutual Info I(X;Y): {:.2} bits ({}ms)\n",
        rep.total_functions,
        rep.total_mcmc_samples,
        rep.max_output_entropy_bits,
        rep.max_mutual_info_bits,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [E[Y]={:.2} | σ={:.2} | 90% CI={} | H(X)={:.2}b | H(Y)={:.2}b | I(X;Y)={:.2}b | L_∞={:.2}b]",
            f.signature,
            f.posterior_mean,
            f.posterior_std_dev,
            f.credible_interval_90,
            f.input_shannon_entropy_bits,
            f.output_shannon_entropy_bits,
            f.mutual_information_bits,
            f.min_entropy_leakage_bits
        );
        for h in &f.posterior_histogram {
            println!(
                "  {} | p={:<4.2} ({:>3}) | {}",
                h.bucket_label, h.probability, h.count, h.ascii_bar
            );
        }
        println!();
    }

    if rep.total_functions == 0 {
        return Err("probabilistic entropy analyzer found 0 functions".to_string());
    }
    Ok(())
}

fn run_quantum_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.quantum_circuit();
    println!(
        "=== Reversible Bennett-Toffoli Quantum Circuit Compiler, Uncomputation Verifier & OpenQASM 3.0 Synthesizer: {} ===",
        label
    );
    println!(
        "Functions: {} | Qubits Allocated: {} | Reversible Gates: {} | Toffoli: {} | Clifford+T: {} | Garbage-Free Uncomputed: {} | Max Grover Speedup: {:.2}x ({}ms)\n",
        rep.total_functions,
        rep.total_qubits_allocated,
        rep.total_reversible_gates,
        rep.total_toffoli_gates,
        rep.total_clifford_t_gates,
        rep.all_ancillas_uncomputed,
        rep.max_grover_speedup,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [Qubits: {} ({} logical + {} ancilla) | Gates: {} (F={}, F†={}) | T-count: {} | Grover: {:.2}x ({} iters)]",
            f.signature,
            f.total_qubits,
            f.logical_qubits,
            f.ancilla_qubits,
            f.total_gates,
            f.forward_gates,
            f.uncompute_gates,
            f.clifford_t_count,
            f.grover_quadratic_speedup,
            f.grover_optimal_iterations
        );
        for g in f.gates.iter().take(8) {
            println!(
                "  • [Step #{:<2} · {:<22}] {:<28} ctrl={} -> tgt={} (T={}) — {}",
                g.step_idx,
                g.stage,
                g.gate_op,
                g.control_qubits,
                g.target_qubits,
                g.t_gate_cost,
                g.source_note
            );
        }
        println!("  --- Synthesized OpenQASM 3.0 Source ---\n{}\n", f.openqasm3_source);
    }

    if !rep.all_ancillas_uncomputed {
        return Err("one or more ancilla registers were not cleanly uncomputed".to_string());
    }
    Ok(())
}

fn run_automata_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.minimal_dfa();
    println!(
        "=== Angluin L* Active Automaton Learner, Myhill-Nerode Minimal DFA Synthesizer & 13-Spoke Table Vectorizer: {} ===",
        label
    );
    println!(
        "Functions: {} | Unminimized States: {} -> Minimal States: {} | L* Queries: {} | Branchless Speedup: {:.2}x ({}ms)\n",
        rep.total_functions,
        rep.total_unminimized_states,
        rep.total_minimal_states,
        rep.total_lstar_queries,
        rep.overall_branchless_speedup,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Function: {} [States: {} -> {} | L* Queries: {} | Branchless Speedup: {:.2}x]",
            f.signature,
            f.unminimized_states,
            f.minimal_states,
            f.observation_table_queries,
            f.branchless_speedup
        );
        println!("  Kleene Regex: {}", f.synthesized_regex);
        for w in &f.distinguishability_witnesses {
            println!(
                "  • {} ≢ {} via suffix e='{}': {} vs. {}",
                w.state_a, w.state_b, w.distinguishing_suffix, w.outcome_a, w.outcome_b
            );
        }
        println!();
    }

    if !rep.all_myhill_nerode_minimal {
        return Err("minimal DFA synthesizer failed".to_string());
    }
    Ok(())
}

fn run_hls_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.hls_rtl();
    println!(
        "=== High-Level Synthesis (HLS) Hardware Compiler, ASAP/ALAP Mobility FSMD Scheduler & IEEE-1800 SystemVerilog RTL Generator: {} ===",
        label
    );
    println!(
        "Functions: {} | CDFG Ops: {} | FSMD States: {} | LUT6: {} | Flip-Flops: {} | DSP48E2: {} | BRAM36: {} | Min F_max: {:.1} MHz ({}ms)\n",
        rep.total_functions,
        rep.total_cdfg_ops,
        rep.total_fsmd_states,
        rep.total_lut6,
        rep.total_flip_flops,
        rep.total_dsp48,
        rep.total_bram36,
        rep.min_fmax_mhz,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Module `{}` — {} [Latency: {} cyc | II: {} | CritPath: {:.2}ns | F_max: {:.1} MHz | Area: {} LUT6, {} FF, {} DSP48E2]",
            f.module_name,
            f.signature,
            f.latency_cycles,
            f.initiation_interval,
            f.critical_path_ns,
            f.estimated_fmax_mhz,
            f.lut6_count,
            f.flip_flops_count,
            f.dsp48_blocks
        );
        for op in f.operations.iter().take(8) {
            println!(
                "  • Op #{:<2} [{:<10} · {:<16}] ASAP={} ALAP={} Mobility={} ({:.2}ns) — {}",
                op.op_id,
                op.scheduled_state,
                op.functional_unit,
                op.asap_cycle,
                op.alap_cycle,
                op.mobility,
                op.delay_ns,
                op.source_expr
            );
        }
        println!("  --- Synthesizable IEEE-1800-2017 SystemVerilog RTL ---\n{}", f.systemverilog_rtl);
    }

    if rep.total_functions == 0 || rep.total_cdfg_ops == 0 {
        return Err("HLS SystemVerilog RTL compiler generated 0 operations".to_string());
    }
    Ok(())
}

fn run_gpu_cli(args: &[String]) -> Result<(), String> {
    let mut file_or_preset: Option<&str> = None;
    for a in args {
        if !a.starts_with('-') && file_or_preset.is_none() {
            file_or_preset = Some(a.as_str());
        }
    }

    let (eng, label) = if let Some(p) = file_or_preset {
        if let Some(sample) = find_sample(p) {
            let e = StarEngine::from_source(sample.initial_spoke, sample.source)
                .map_err(|d| d.to_string())?;
            (
                e,
                format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
            )
        } else {
            let (e, spoke) = load_engine_from_path(p)?;
            (e, format!("{} ({})", p, spoke.display_name()))
        }
    } else {
        let sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let rep = eng.gpu_simt();
    println!(
        "=== 32-Lane Warp SIMT GPU Compute Kernel Synthesizer (CUDA PTX / WebGPU WGSL / Metal MSL / OpenCL C): {} ===",
        label
    );
    println!(
        "Functions: {} | GPU Kernels: {} | Avg SM Occupancy: {:.1}% | Avg Warp Efficiency: {:.1}% | Divergence Sites: {} | Bank Conflicts: {} | Max GPU Speedup: {:.1}x ({}ms)\n",
        rep.total_functions,
        rep.total_gpu_kernels,
        rep.avg_sm_occupancy_pct,
        rep.avg_warp_efficiency_pct,
        rep.total_divergence_sites,
        rep.total_bank_conflicts,
        rep.max_gpu_speedup,
        rep.elapsed_ms
    );

    for f in &rep.functions {
        println!(
            "Kernel `{}` — {} [Threads/WG: {} | Regs/Thread: {} | SMEM: {}B | Occupancy: {:.1}% | Warp Eff: {:.1}% | Roofline: {:.2} FLOPs/B ({}) | Speedup: {:.1}x]",
            f.kernel_name,
            f.signature,
            f.workgroup_threads,
            f.registers_per_thread,
            f.shared_mem_bytes,
            f.sm_occupancy_pct,
            f.warp_efficiency_pct,
            f.arithmetic_intensity_flops_per_byte,
            f.roofline_bound,
            f.estimated_gpu_speedup
        );
        for d in &f.divergence_sites {
            println!(
                "  • Warp Branch #{} [{}] taken={}/32 not_taken={}/32 mask={} serial={}x ({:.1}%) — {}",
                d.branch_id,
                d.condition_expr,
                d.active_lanes_taken,
                d.active_lanes_not_taken,
                d.active_mask_hex,
                d.serialization_factor,
                d.simd_efficiency_pct,
                d.mitigation_note
            );
        }
        println!("  --- Synthesized CUDA C++/PTX & WebGPU WGSL Kernels ---\n{}\n\n{}\n", f.cuda_ptx_source, f.webgpu_wgsl_source);
    }

    if rep.total_gpu_kernels == 0 || rep.total_bank_conflicts > 0 {
        return Err("GPU SIMT compiler failed or had unresolved shared-memory bank conflicts".to_string());
    }
    Ok(())
}

fn run_mutate_cli(args: &[String]) -> Result<(), String> {
    let mut file_path: Option<&str> = None;
    let mut harden = false;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--harden" | "-H" => {
                harden = true;
                i += 1;
            }
            "--to" | "-t" => {
                i += 2;
            }
            other if !other.starts_with('-') && file_path.is_none() => {
                file_path = Some(other);
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }

    let (mut eng, src_spoke, label) = if let Some(p) = file_path {
        let (e, spoke) = load_engine_from_path(p)?;
        (e, spoke, format!("{} ({})", p, spoke.display_name()))
    } else {
        let sample = find_sample("alerts").ok_or("missing alerts sample")?;
        let e = StarEngine::from_source(sample.initial_spoke, sample.source)
            .map_err(|d| d.to_string())?;
        (
            e,
            sample.initial_spoke,
            format!("preset '{}' ({})", sample.id, sample.initial_spoke.display_name()),
        )
    };

    let out_spoke = parse_target_spoke(args)?.unwrap_or(src_spoke);

    if !harden {
        let rep = eng.mutate();
        println!("=== Hub AST Mutation Testing: {} ===", label);
        println!(
            "Mutation Score: {}% ({}/{} killed, {} survived in {}ms)",
            rep.score_pct, rep.killed, rep.total_mutants, rep.survived, rep.elapsed_ms
        );
        if rep.survived > 0 {
            println!("\nSurviving Mutants ({}):", rep.survived);
            for m in rep.survivors() {
                println!("  ⚠ [mutant #{} in {}()] {}", m.id, m.func, m.description);
            }
            println!("\nTip: run `cargo run -- mutate --harden` to synthesize boundary assertions across all 11 languages.");
        } else {
            println!("\n✓ 0 surviving mutants — unit test suite killed 100% of Hub mutants.");
        }
        return Ok(());
    }

    let (snap, hrep) = eng.harden_tests();
    println!("=== Hub AST Mutation Testing & Auto-Test Hardening: {} ===", label);
    println!(
        "Before Hardening: {}% ({}/{} killed, {} survived)",
        hrep.before.score_pct, hrep.before.killed, hrep.before.total_mutants, hrep.before.survived
    );
    println!(
        "After Hardening:  {}% ({}/{} killed, {} survived) — synthesized {} boundary assertion(s)",
        hrep.after.score_pct,
        hrep.after.killed,
        hrep.after.total_mutants,
        hrep.after.survived,
        hrep.added_assertions
    );
    let passed = snap.test_results.iter().filter(|t| t.passed).count();
    println!(
        "Polyglot Unit Tests: {}/{} passed via Hub VM\n",
        passed,
        snap.test_results.len()
    );
    println!(
        "--- Hardened {} View (.{}) ---",
        out_spoke.display_name(),
        out_spoke.extension()
    );
    print!("{}", eng.project(out_spoke));
    Ok(())
}

fn run_fuzz_cli(args: &[String]) -> Result<(), String> {
    let mut count = 50usize;
    let mut seed: u64 = 0x57A4_2026_0500;
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--seed" {
            let s = args
                .get(i + 1)
                .ok_or_else(|| "expected integer after --seed".to_string())?;
            seed = s
                .parse::<u64>()
                .map_err(|_| format!("invalid seed '{}'", s))?;
            i += 2;
            continue;
        }
        if let Ok(c) = args[i].parse::<usize>() {
            count = c;
        }
        i += 1;
    }

    let report = run_fuzz_suite(seed, count);
    println!(
        "★ Property-Based 13-Spoke Lens Fuzzer (seed=0x{:x}, programs={}):",
        report.seed, report.programs_tested
    );
    println!(
        "  • 13-spoke GetPut + cold Put round-trips: {}",
        report.spoke_roundtrips
    );
    println!(
        "  • Synthesized unit test suites passed:   {}",
        report.assertions_passed
    );
    println!(
        "  • Hub optimizer equivalence checks:      {}",
        report.optimizer_checks
    );
    println!("  • Elapsed time:                          {}ms", report.elapsed_ms);

    if report.ok() {
        println!("✓ 0 lens, typecheck, VM, or optimizer counterexamples found.");
        Ok(())
    } else {
        for f in &report.failures {
            eprintln!("\n[FAILURE] {}", f);
        }
        Err(format!("{} fuzz failure(s)", report.failures.len()))
    }
}

fn run_refactor(args: &[String]) -> Result<(), String> {
    if args.len() < 3 {
        return Err(
            "usage: starlang refactor <file> <symbol> <new_name> [--to rust|zig|c|cpp|swift|java|go|python|ruby|ts|star]"
                .to_string(),
        );
    }
    let (mut eng, src_spoke) = load_engine_from_path(&args[0])?;
    let (_, count) = eng.rename_symbol(&args[1], &args[2])?;
    let out_spoke = parse_target_spoke(&args[3..])?.unwrap_or(src_spoke);
    eprintln!(
        "✓ Renamed {} occurrence(s) on Hub -> projecting {}:",
        count,
        out_spoke.display_name()
    );
    print!("{}", eng.project(out_spoke));
    Ok(())
}

fn run_optimize(args: &[String]) -> Result<(), String> {
    let input = args.first().ok_or_else(|| {
        "usage: starlang optimize <file> [--to rust|zig|c|cpp|swift|java|go|python|ruby|ts|star]"
            .to_string()
    })?;
    let (mut eng, src_spoke) = load_engine_from_path(input)?;
    let (_, rewrites) = eng.optimize();
    let out_spoke = parse_target_spoke(&args[1..])?.unwrap_or(src_spoke);
    eprintln!(
        "⚡ Applied {} semantic optimization(s) on Hub -> projecting {}:",
        rewrites,
        out_spoke.display_name()
    );
    print!("{}", eng.project(out_spoke));
    Ok(())
}

fn run_file_all_compilers(args: &[String]) -> Result<(), String> {
    let input = args
        .first()
        .ok_or_else(|| "usage: starlang run <file>".to_string())?;
    let (eng, _) = load_engine_from_path(input)?;
    let report = run_all_spokes(&eng);
    for r in &report.results {
        println!(
            "[{}] ({}ms, ok={}):\n{}",
            r.language,
            r.duration_ms,
            r.ok,
            r.stdout.trim()
        );
        if !r.stderr.trim().is_empty() {
            eprintln!("  stderr: {}", r.stderr.trim());
        }
    }
    println!(
        "\nParallel wall time: {}ms | Outputs match across all 14 engines: {}",
        report.wall_time_ms, report.outputs_match
    );
    if !report.outputs_match {
        return Err("outputs diverged or execution failed".to_string());
    }
    Ok(())
}

fn print_help() {
    println!(
        "starlang v2.5 — 13-Spoke Bidirectional Compiler, WebAssembly, Time-Travel, Big-O, QuickCheck, Auto-Repair, PBE Synth, SSA, Hoare, Concolic, Taint, E-Graph, Partial Eval, Polyhedral SIMD, WCET, RegAlloc, Escape, Superscalar CPU/Cache/Branch Sim, List Scheduler, Forward/Reverse AutoDiff, Lipschitz Stability, Lamport Vector-Clock Actor Verifier, TLA+ Model Checker, ZK R1CS Circuit Prover, Relational SQL Optimizer, Liquid Refinement Types, Probabilistic MCMC/Entropy, Reversible Quantum Circuit Compiler, Minimal DFA Synthesizer, High-Level Synthesis (HLS) SystemVerilog RTL Compiler & SIMT GPU Kernel Synthesizer Studio (Rust <-> Zig 0.16 <-> C11 <-> C++ <-> Swift 6 <-> Java 21 <-> Go <-> Python <-> Ruby <-> LuaJIT <-> Perl 5 <-> TypeScript <-> Star IR -> Wasm / AArch64 / x86_64 / Circom / SQL / OpenQASM 3 / SystemVerilog RTL / CUDA / WGSL / Metal / OpenCL)

USAGE:
  cargo run                                         Start the 13-pane live web studio on http://127.0.0.1:7878
  cargo run -- serve --port 8080                    Start the live web studio on a custom port
  cargo run -- watch [dir] [stem]                   Live-sync .rs, .zig, .c, .cpp, .swift, .java, .go, .py, .rb, .lua, .pl, .ts, .star files
  cargo run -- convert <file> [--to perl]           Transpile a file into one or all other spokes
  cargo run -- hls [file|preset]                    Compile Hub AST to High-Level Synthesis (HLS) ASAP/ALAP FSMD & IEEE-1800 SystemVerilog RTL
  cargo run -- gpu [file|preset]                    Synthesize 32-Lane Warp SIMT GPU Kernels (CUDA PTX, WebGPU WGSL, Metal MSL, OpenCL C)
  cargo run -- quantum [file|preset]                Compile Reversible Bennett-Toffoli Quantum Circuits (F->Copy->F†) & OpenQASM 3.0
  cargo run -- automata [file|preset]               Run Angluin L* Active Learner, Myhill-Nerode Minimal DFA & 13-Spoke Lookup Tables
  cargo run -- refinement [file|preset]             Infer Liquid Refinement Types ({{ ν: T | φ(ν) }}), solve CHCs & emit 13-Spoke Refined Types
  cargo run -- prob [file|preset]                   Run Metropolis-Hastings MCMC sampler & compute Shannon Entropy H(X)/H(Y) & Mutual Info I(X;Y)
  cargo run -- zk [file|preset]                     Run Rank-1 Constraint System (R1CS) ZK Circuit Compiler, Witness Verifier & Circom Synth
  cargo run -- sql [file|preset]                    Run Relational Algebra (σ, π, Γ), Selection Pushdown & Vectorized SQL / DataFrame Optimizer
  cargo run -- actors [file|preset]                 Run Lamport Vector-Clock Happens-Before Race Detector, Deadlock Prover & 13-Spoke Actors
  cargo run -- modelcheck [file|preset]             Run Explicit-State Bounded Model Checker, Temporal Safety/Liveness & TLA+ Spec Synth
  cargo run -- autodiff [file|preset] [--inject]    Run Forward-Mode Dual & Reverse-Mode Wengert-Tape AutoDiff + 13-Spoke Gradient Synth
  cargo run -- stability [file|preset]              Run IEEE-754 / Fixed-Point Numerical Stability, Condition κ & Lipschitz Bound Auditor
  cargo run -- microarch [file|preset]              Run 4-Wide Out-of-Order Superscalar CPU, 2-Bit Branch Predictor & 8-Way L1D Cache Sim
  cargo run -- schedule [file|preset]               Run Gibbons-Muchnick Critical-Path DAG List Instruction Scheduler & Stall Eliminator
  cargo run -- regalloc [file|preset] [-k N]        Run Chaitin-Briggs Kempe Graph-Coloring & Linear-Scan RegAlloc + AArch64/x86_64 ASM
  cargo run -- escape [file|preset]                 Run Interprocedural Escape Analysis, Scalar Replacement (SROA) & RVO Optimizer
  cargo run -- polyhedral [file|preset]             Run Polyhedral Loop Dependence, Monoid Reduction & 13-Spoke SIMD Vectorizer
  cargo run -- wcet [file|preset]                   Run Floyd-Turing Ranking Termination Prover & IPET Symbolic BCET/WCET Analyzer
  cargo run -- egraph [file|preset] [--apply]       Run Equality Saturation & Congruence-Closure E-Graph Superoptimizer
  cargo run -- peval [file|preset] [--apply]        Run Futamura Partial Evaluator, Constant/Enum Specializer & Loop Unroller
  cargo run -- concolic [file|preset] [--inject]    Explore execution paths via boundary-negation solver & synthesize path-covering tests
  cargo run -- security [file|preset]               Audit Denning lattice taint flows, dominating sanitizers & constant-time side-channels
  cargo run -- ssa [file|preset]                    Compute Cytron SSA form, Dominance Frontiers, φ-nodes, Liveness & Def-Use chains
  cargo run -- contracts [file|preset]              Infer Hoare-Logic DbC contracts (requires/invariant/ensures) & verify WP VCs
  cargo run -- synth [spec|sum_above]               Synthesize a verified polyglot function from I/O examples across all 13 spokes
  cargo run -- cfg [file|preset] [--dot]            Analyze Control-Flow Graphs, Dominator sets, Natural Loops & Mermaid/DOT
  cargo run -- debug [file|preset] [--slice var]    Record time-travel trace across all 13 languages & compute backward causal slice
  cargo run -- complexity [file|preset]             Profile static & empirical Big-O scaling, gas cost & 13-spoke code density
  cargo run -- quickcheck [file|preset] [--trials N] Run property-based QuickCheck, invariant discovery & counterexample shrinking
  cargo run -- repair [file|preset]                 Localize faults via backward slicing & synthesize a 4-gate verified AST patch
  cargo run -- equiv <left_file> <right_file>       Verify De Bruijn α-equivalence & QuickCheck bisimulation across any two files
  cargo run -- wasm [file] [--wat] [--out a.wasm]   Compile Hub AST to W3C WebAssembly 1.0 (.wasm + .wat) & run in V8 JIT
  cargo run -- diff <left_file> <right_file>        Compute pure semantic Hub AST delta across any two languages
  cargo run -- merge [base left right] [--to X]     3-way concurrent cross-language Hub AST + metadata merger
  cargo run -- check <file>                         Run the central Hub static type & scope checker
  cargo run -- verify [file]                        Prove safety obligations & detect UNSAT dead branches via Hub abstract interpretation
  cargo run -- eval <file>                          Execute main() instantly in the native in-memory Hub VM
  cargo run -- test <file>                          Execute polyglot unit tests instantly in the Hub VM
  cargo run -- trace [file]                         Report Hub AST statement coverage %, hotspots & call trace
  cargo run -- mutate [file] [--harden] [--to X]    Run Hub AST mutation testing & auto-harden boundary tests
  cargo run -- fuzz [count] [--seed N]              Run property-based 13-spoke GetPut & VM equivalence fuzzer
  cargo run -- refactor <file> <sym> <new> [--to X] Scope-aware cross-language symbol rename
  cargo run -- optimize <file> [--to X]             Constant-fold & prune dead branches via the Hub
  cargo run -- run <file>                           Verify across Hub VM + Wasm + rustc + zig + clang + clang++ + swiftc + javac + go + py + ruby + luajit + perl + node
  cargo run -- demo                                 Run an end-to-end 13-spoke sync, Wasm JIT, time-travel, Big-O, QuickCheck, repair, synth, SSA & 14-engine demo"
    );
}

fn run_cli_demo() -> Result<(), String> {
    let sample = find_sample("alerts").ok_or("missing alerts sample")?;
    println!("=== 1. Seeding Central Hub from Rust ({}) ===", sample.title);
    let mut engine =
        StarEngine::from_source(sample.initial_spoke, sample.source).map_err(|d| d.to_string())?;
    let init_snap = engine.snapshot();
    let passed_tests = init_snap.test_results.iter().filter(|t| t.passed).count();
    println!(
        "Hub initialized: {} AST nodes | Safety: {}/{} proven | Coverage: {}% ({}/{}) | Tests: {}/{} passed | Hub VM: {}\n",
        init_snap.node_count,
        init_snap.safety_proven,
        init_snap.safety_total,
        init_snap.coverage_pct,
        init_snap.covered_stmts,
        init_snap.total_stmts,
        passed_tests,
        init_snap.test_results.len(),
        init_snap.live_eval.stdout.trim()
    );

    let zig_before = engine.project(SpokeId::Zig);
    println!("--- Projected Zig 0.16 View ---\n{}", zig_before);

    println!("=== 2. 3-Way Concurrent Polyglot Merge (Zig 0.16 + Python off Shared Rust Base) ===");
    let zig_fork = zig_before.replace(
        "        Severity.Critical => {\n            return 5;\n        },",
        "        Severity.Critical => {\n            // Escalated critical weight in Zig 0.16\n            return 10;\n        },",
    );
    let py_fork = engine.project(SpokeId::Python).replace(
        "        if ms < 0:\n            continue",
        "        # Skip negative jitter samples in Python\n        if ms < 0:\n            continue",
    );
    let (_, mrep) = engine
        .merge_concurrent(SpokeId::Zig, &zig_fork, SpokeId::Python, &py_fork)
        .map_err(|d| d.to_string())?;
    println!(
        "Clean 3-way merge: {} | Applied {} concurrent cross-language edit(s) | Conflicts: {}\n",
        mrep.clean,
        mrep.applied_changes.len(),
        mrep.conflicts.len()
    );

    println!("=== 3. Cross-Language Hub Refactor: `Severity::Critical` -> `Severity::Emergency` ===");
    let (snap, renamed_sites) = engine.rename_symbol("Severity::Critical", "Emergency")?;
    let passed_after = snap.test_results.iter().filter(|t| t.passed).count();
    println!(
        "Renamed {} AST sites across all 13 languages | Coverage: {}% | Tests: {}/{} passed | Live Hub VM: {}\n",
        renamed_sites,
        snap.coverage_pct,
        passed_after,
        snap.test_results.len(),
        snap.live_eval.stdout.trim()
    );

    println!("=== 4. Hub AST Mutation Testing & Auto-Test Hardening Across All 13 Languages ===");
    let (hardened_snap, hrep) = engine.harden_tests();
    let hardened_passed = hardened_snap
        .test_results
        .iter()
        .filter(|t| t.passed)
        .count();
    println!(
        "Mutation Score: {}% -> {}% ({}/{} mutants killed; synthesized {} boundary assertion(s); {}/{} tests pass)\n",
        hrep.before.score_pct,
        hrep.after.score_pct,
        hrep.after.killed,
        hrep.after.total_mutants,
        hrep.added_assertions,
        hardened_passed,
        hardened_snap.test_results.len()
    );

    println!("=== 5. Hub Symbolic Safety & Dead-Branch Verifier (`ringbuf` Zig 0.16 preset) ===");
    let rb_sample = find_sample("ringbuf").ok_or("missing ringbuf sample")?;
    let rb_eng = StarEngine::from_source(rb_sample.initial_spoke, rb_sample.source)
        .map_err(|d| d.to_string())?;
    let vrep = rb_eng.verify();
    println!(
        "Proven Safe: {}/{} obligations ({}ms) | Refuted: {} | UNSAT Dead Branches: {}",
        vrep.proven_safe,
        vrep.total_obligations,
        vrep.elapsed_ms,
        vrep.refuted,
        vrep.unreachable_branches.len()
    );
    for ob in &vrep.obligations {
        println!(
            "  ✓ [{}()] {}: {} — {}",
            ob.func,
            ob.kind.label(),
            ob.expr_summary,
            ob.proof_note
        );
    }
    println!();

    println!("=== 6. Zero-Dependency Hub -> WebAssembly 1.0 (.wasm + .wat) & V8 JIT (`backoff` LuaJIT preset) ===");
    let bo_sample = find_sample("backoff").ok_or("missing backoff sample")?;
    let bo_eng = StarEngine::from_source(bo_sample.initial_spoke, bo_sample.source)
        .map_err(|d| d.to_string())?;
    let bo_wasm = bo_eng.compile_wasm()?;
    let bo_jit = bo_eng.run_wasm();
    println!(
        "Compiled .wasm: {} bytes (Code: {}B, Data: {}B, {} functions) | V8 Wasm JIT ({}ms): {}/{} tests passed | stdout: {}\n",
        bo_wasm.bytes.len(),
        bo_wasm.code_bytes,
        bo_wasm.data_bytes,
        bo_wasm.func_count,
        bo_jit.duration_ms,
        bo_jit.tests_passed,
        bo_jit.tests_total,
        bo_jit.stdout.trim()
    );
    if !bo_jit.ok {
        return Err(format!("Wasm JIT failed on backoff: {:?}", bo_jit.error));
    }

    println!("=== 7. Polyglot Time-Travel Debugger, Big-O Profiler & QuickCheck (`ratelimit` Perl 5.34 preset) ===");
    let rl_sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source)
        .map_err(|d| d.to_string())?;
    let drep = rl_eng.time_travel(Some("avg_cost"));
    let slice_len = drep.slice.as_ref().map(|s| s.slice_steps.len()).unwrap_or(0);
    let crep = rl_eng.complexity();
    let qrep = rl_eng.quickcheck(Some(32));
    let cfg_rep = rl_eng.cfg();
    let ssa_rep = rl_eng.ssa();
    let hoare_rep = rl_eng.contracts();
    let sec_rep = rl_eng.security_flow();
    let mut repair_eng = rl_eng;
    let (peval_rep, _) = repair_eng.partial_eval(false);
    let (conc_rep, _) = repair_eng.concolic(false);
    let (_, rrep, _) = repair_eng.repair(true);
    let (srep, _) = repair_eng.synthesize(None, false)?;
    let pipe_sample = find_sample("pipeline").ok_or("missing pipeline sample")?;
    let mut pipe_eng = StarEngine::from_source(pipe_sample.initial_spoke, pipe_sample.source)
        .map_err(|d| d.to_string())?;
    let (eg_rep, _) = pipe_eng.egraph(false);
    let poly_rep = pipe_eng.polyhedral();
    let wcet_rep = repair_eng.termination_wcet();
    let reg_rep = repair_eng.regalloc(Some(8));
    let esc_rep = repair_eng.escape_analysis();
    let uarch_rep = repair_eng.microarch();
    let sched_rep = repair_eng.schedule_instructions();
    let (ad_rep, _) = pipe_eng.autodiff(false);
    let stab_rep = repair_eng.numerical_stability();
    let act_rep = repair_eng.actors();
    let mc_rep = repair_eng.model_check();
    let zk_rep = repair_eng.zk_r1cs();
    let sql_rep = repair_eng.relational_sql();
    let ref_rep = repair_eng.liquid_refinements();
    let prob_rep = repair_eng.probabilistic_entropy();
    let q_rep = repair_eng.quantum_circuit();
    let dfa_rep = repair_eng.minimal_dfa();
    let hls_rep = repair_eng.hls_rtl();
    let gpu_rep = repair_eng.gpu_simt();
    println!(
        "Recorded {} steps (max depth {}) across 13 languages | Backward slice for 'avg_cost': {} causal steps | stdout: {}",
        drep.total_steps,
        drep.max_depth,
        slice_len,
        drep.final_stdout.trim()
    );
    println!(
        "Dominant Big-O: {} (Max Cyclomatic: {}, Gas: {}) | QuickCheck: {}/{} trials passed ({} algebraic invariants) | CEGIS Auto-Repair: {} ({} candidates) | PBE Synth: {} ({} pruned) | CFG: {} blocks, {} loop(s) | SSA: {} φ-nodes, {} defs | Hoare WP: {}/{} VCs proven | Concolic: {} paths ({}% branch cov) | Security Taint: {}/{} sinks guarded | E-Graph: {} classes, {} gas saved | Partial Eval: {} specialized call(s), steps {}->{} | Polyhedral SIMD: {}/{} vectorizable ({:.2}x SIMD4) | Termination/WCET: {}/{} loops proven, WCET(64)={}c | RegAlloc(K=8): {} vregs, {} spills, {} ARM64 / {} x86_64 insts | Escape/SROA: {}B saved/run ({}% heap elision) | Superscalar OoO Sim: {} μops, IPC {:.2}, {:.1}% branch acc, {:.1}% L1D hit | List Scheduler: {}c->{}c (-{} stall bubbles) | AutoDiff: {}/{} partials verified, `{}` | Stability: max κ={:.2}, L={:.2} | Actors: {} stages, {} VC events, DRF={} | TLA+ BMC: {} states, {}/{} temporal properties | ZK R1CS: {} wires, {}/{} constraints SAT | Relational SQL: {} pushdown(s), {:.2}x columnar speedup | Liquid Types: {} bindings, {}/{} CHCs | Probabilistic QIF: {} MCMC samples, max I(X;Y)={:.2}b | Quantum: {}q, {} gates, Grover {:.2}x | Minimal DFA: {}->{} states ({:.2}x branchless) | HLS RTL: {} ops, {} states, {} LUT6, {:.1} MHz | GPU SIMT: {} kernels, {:.1}% warp eff, {:.1}x speedup\n",
        crep.dominant_big_o,
        crep.max_cyclomatic,
        crep.module_gas.total_gas,
        qrep.optimizer_checks,
        qrep.total_trials,
        qrep.total_invariants,
        rrep.repaired,
        rrep.candidates_evaluated,
        srep.fn_name,
        srep.pruned_by_obs_equiv,
        cfg_rep.total_blocks,
        cfg_rep.total_natural_loops,
        ssa_rep.total_phi_nodes,
        ssa_rep.total_ssa_defs,
        hoare_rep.proven_vcs,
        hoare_rep.total_vcs,
        conc_rep.total_paths,
        conc_rep.branch_coverage_pct,
        sec_rep.safe_sinks,
        sec_rep.total_sinks,
        eg_rep.total_eclasses,
        eg_rep.gas_saved,
        peval_rep.specialized_calls,
        peval_rep.vm_steps_before,
        peval_rep.vm_steps_after,
        poly_rep.vectorizable_loops,
        poly_rep.total_loops,
        poly_rep.max_simd4_speedup,
        wcet_rep.proven_terminating_loops,
        wcet_rep.total_loops_audited,
        wcet_rep.module_wcet_cycles_n64,
        reg_rep.total_virtual_regs,
        reg_rep.total_spills,
        reg_rep.total_aarch64_insts,
        reg_rep.total_x86_64_insts,
        esc_rep.total_bytes_saved_per_run,
        esc_rep.heap_reduction_pct,
        uarch_rep.total_uops_retired,
        uarch_rep.superscalar_ipc,
        uarch_rep.branch_accuracy_pct,
        uarch_rep.l1d_hit_rate_pct,
        sched_rep.total_cycles_before,
        sched_rep.total_cycles_after,
        sched_rep.total_bubbles_eliminated,
        ad_rep.verified_partials,
        ad_rep.total_partials,
        ad_rep.synthesized_grad_fn_name,
        stab_rep.max_condition_number,
        stab_rep.max_lipschitz_constant,
        act_rep.total_actor_stages,
        act_rep.total_vc_events,
        act_rep.all_data_race_free,
        mc_rep.total_reachable_states,
        mc_rep.verified_properties,
        mc_rep.total_properties,
        zk_rep.total_wires,
        zk_rep.satisfied_constraints,
        zk_rep.total_constraints,
        sql_rep.total_pushed_predicates,
        sql_rep.overall_columnar_speedup,
        ref_rep.total_refined_bindings,
        ref_rep.discharged_horn_clauses,
        ref_rep.total_horn_clauses,
        prob_rep.total_mcmc_samples,
        prob_rep.max_mutual_info_bits,
        q_rep.total_qubits_allocated,
        q_rep.total_reversible_gates,
        q_rep.max_grover_speedup,
        dfa_rep.total_unminimized_states,
        dfa_rep.total_minimal_states,
        dfa_rep.overall_branchless_speedup,
        hls_rep.total_cdfg_ops,
        hls_rep.total_fsmd_states,
        hls_rep.total_lut6,
        hls_rep.min_fmax_mhz,
        gpu_rep.total_gpu_kernels,
        gpu_rep.avg_warp_efficiency_pct,
        gpu_rep.max_gpu_speedup
    );
    if !drep.ok
        || slice_len == 0
        || !qrep.all_passed
        || !rrep.repaired
        || !srep.ok
        || cfg_rep.total_blocks == 0
        || ssa_rep.total_phi_nodes == 0
        || !hoare_rep.all_verified
        || conc_rep.total_paths == 0
        || !sec_rep.all_sinks_safe
        || !eg_rep.translation_validated
        || !peval_rep.translation_validated
        || poly_rep.vectorizable_loops == 0
        || !wcet_rep.all_terminating
        || reg_rep.total_virtual_regs == 0
        || esc_rep.total_bytes_saved_per_run == 0
        || uarch_rep.total_uops_retired == 0
        || sched_rep.total_instructions == 0
        || !ad_rep.all_gradients_verified
        || stab_rep.total_functions == 0
        || !act_rep.all_data_race_free
        || !mc_rep.all_verified
        || !zk_rep.all_circuits_satisfied
        || sql_rep.query_lifted_functions == 0
        || !ref_rep.all_subtypes_verified
        || prob_rep.total_mcmc_samples == 0
        || !q_rep.all_ancillas_uncomputed
        || !dfa_rep.all_myhill_nerode_minimal
        || hls_rep.total_cdfg_ops == 0
        || gpu_rep.total_gpu_kernels == 0
        || gpu_rep.total_bank_conflicts > 0
    {
        return Err("Time-travel debugger, QuickCheck, Auto-Repair, PBE Synth, CFG, SSA, Hoare WP, Concolic, Security Taint, E-Graph, Partial Eval, Polyhedral SIMD, Termination/WCET, RegAlloc, Escape Analysis, Superscalar CPU Sim, List Scheduler, AutoDiff, Numerical Stability, Actor Concurrency, TLA+ Model Checker, ZK R1CS Prover, Relational SQL Optimizer, Liquid Refinement Prover, Probabilistic Entropy Analyzer, Quantum Circuit Compiler, Minimal DFA Synthesizer, HLS SystemVerilog Compiler, or SIMT GPU Kernel Synthesizer failed".to_string());
    }

    println!("=== 8. Differential Execution Across All 14 Engines (Hub VM + Wasm V8 JIT + rustc + zig + clang -std=c11 + clang++ PCH + swiftc + javac + go + python3 + ruby + luajit + perl + node) ===");
    let report = run_all_spokes(&engine);
    for r in &report.results {
        println!(
            "[{}] ({}ms, ok={}): {}",
            r.language,
            r.duration_ms,
            r.ok,
            r.stdout.trim()
        );
        if !r.stderr.trim().is_empty() {
            println!("  stderr: {}", r.stderr.trim());
        }
    }
    println!(
        "\nParallel wall time: {}ms | Byte-for-byte match across all 14 engines: {}",
        report.wall_time_ms, report.outputs_match
    );
    if !report.outputs_match {
        return Err("runtime outputs diverged".to_string());
    }

    println!("\n=== 9. Property-Based 13-Spoke Lens Fuzzer (25 Synthesized Programs × 13 Spokes) ===");
    let fuzz = run_fuzz_suite(0x57A4_2026_0500, 25);
    println!(
        "Verified {} GetPut round-trips & {} test suites in {}ms — Failures: {}",
        fuzz.spoke_roundtrips,
        fuzz.assertions_passed,
        fuzz.elapsed_ms,
        fuzz.failures.len()
    );
    if !fuzz.ok() {
        return Err(format!("fuzzer failures: {:?}", fuzz.failures));
    }

    Ok(())
}

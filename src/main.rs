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
        "starlang v1.0 — 13-Spoke Bidirectional Compiler, WebAssembly & Time-Travel Studio (Rust <-> Zig 0.16 <-> C11 <-> C++ <-> Swift 6 <-> Java 21 <-> Go <-> Python <-> Ruby <-> LuaJIT <-> Perl 5 <-> TypeScript <-> Star IR -> Wasm)

USAGE:
  cargo run                                         Start the 13-pane live web studio on http://127.0.0.1:7878
  cargo run -- serve --port 8080                    Start the live web studio on a custom port
  cargo run -- watch [dir] [stem]                   Live-sync .rs, .zig, .c, .cpp, .swift, .java, .go, .py, .rb, .lua, .pl, .ts, .star files
  cargo run -- convert <file> [--to perl]           Transpile a file into one or all other spokes
  cargo run -- debug [file|preset] [--slice var]    Record time-travel trace across all 13 languages & compute backward causal slice
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
  cargo run -- demo                                 Run an end-to-end 13-spoke sync, Wasm JIT, time-travel debug, 3-way merge, verify, mutate, fuzz & 14-engine demo"
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

    println!("=== 7. Polyglot Time-Travel Debugger & Backward Causal Slicer (`ratelimit` Perl 5.34 preset) ===");
    let rl_sample = find_sample("ratelimit").ok_or("missing ratelimit sample")?;
    let rl_eng = StarEngine::from_source(rl_sample.initial_spoke, rl_sample.source)
        .map_err(|d| d.to_string())?;
    let drep = rl_eng.time_travel(Some("avg_cost"));
    let slice_len = drep.slice.as_ref().map(|s| s.slice_steps.len()).unwrap_or(0);
    println!(
        "Recorded {} steps (max depth {}) across 13 languages | Backward slice for 'avg_cost': {} causal steps | stdout: {}\n",
        drep.total_steps,
        drep.max_depth,
        slice_len,
        drep.final_stdout.trim()
    );
    if !drep.ok || slice_len == 0 {
        return Err("Time-travel debugger check failed on ratelimit".to_string());
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

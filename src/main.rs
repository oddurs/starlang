use std::env;
use std::fs;
use std::path::Path;

use starlang::engine::StarEngine;
use starlang::eval::{eval_module_default, eval_tests_default};
use starlang::fuzzer::run_fuzz_suite;
use starlang::lens::SpokeId;
use starlang::runner::run_all_spokes;
use starlang::samples::find_sample;
use starlang::server::serve_web_studio;
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
        "usage: starlang convert <file> [--to rust|cpp|swift|java|go|python|ruby|ts|star]".to_string()
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
            println!("\nTip: run `cargo run -- mutate --harden` to synthesize boundary assertions across all 9 languages.");
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
        "★ Property-Based 9-Spoke Lens Fuzzer (seed=0x{:x}, programs={}):",
        report.seed, report.programs_tested
    );
    println!(
        "  • 9-spoke GetPut + cold Put round-trips: {}",
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
            "usage: starlang refactor <file> <symbol> <new_name> [--to rust|cpp|swift|java|go|python|ruby|ts|star]"
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
        "usage: starlang optimize <file> [--to rust|cpp|swift|java|go|python|ruby|ts|star]"
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
        "\nParallel wall time: {}ms | Outputs match across all 9 engines: {}",
        report.wall_time_ms, report.outputs_match
    );
    if !report.outputs_match {
        return Err("outputs diverged or execution failed".to_string());
    }
    Ok(())
}

fn print_help() {
    println!(
        "starlang v0.6 — 9-Spoke Bidirectional Compiler (Rust <-> C++ <-> Swift 6 <-> Java 21 <-> Go <-> Python <-> Ruby <-> TypeScript <-> Star IR)

USAGE:
  cargo run                                         Start the 9-pane live web studio on http://127.0.0.1:7878
  cargo run -- serve --port 8080                    Start the live web studio on a custom port
  cargo run -- watch [dir] [stem]                   Live-sync .rs, .cpp, .swift, .java, .go, .py, .rb, .ts, .star files
  cargo run -- convert <file> [--to ruby]           Transpile a file into one or all other spokes
  cargo run -- check <file>                         Run the central Hub static type & scope checker
  cargo run -- eval <file>                          Execute main() instantly in the native in-memory Hub VM
  cargo run -- test <file>                          Execute polyglot unit tests instantly in the Hub VM
  cargo run -- trace [file]                         Report Hub AST statement coverage %, hotspots & call trace
  cargo run -- mutate [file] [--harden] [--to X]    Run Hub AST mutation testing & auto-harden boundary tests
  cargo run -- fuzz [count] [--seed N]              Run property-based 9-spoke GetPut & VM equivalence fuzzer
  cargo run -- refactor <file> <sym> <new> [--to X] Scope-aware cross-language symbol rename
  cargo run -- optimize <file> [--to X]             Constant-fold & prune dead branches via the Hub
  cargo run -- run <file>                           Verify across Hub VM + rustc + clang++ + swiftc + javac + go + py + ruby + node
  cargo run -- demo                                 Run an end-to-end 9-spoke sync, mutation harden, fuzz & 9-engine demo"
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
        "Hub initialized: {} AST nodes | Coverage: {}% ({}/{}) | Tests: {}/{} passed | Hub VM: {}\n",
        init_snap.node_count,
        init_snap.coverage_pct,
        init_snap.covered_stmts,
        init_snap.total_stmts,
        passed_tests,
        init_snap.test_results.len(),
        init_snap.live_eval.stdout.trim()
    );

    let ruby_before = engine.project(SpokeId::Ruby);
    println!("--- Projected Modern Ruby + RBS View ---\n{}", ruby_before);

    println!("=== 2. Editing in Ruby (escalating Critical weight 5 -> 10) ===");
    let ruby_edited = ruby_before.replace(
        "  when Severity::Critical\n    return 5",
        "  when Severity::Critical\n    # Escalated critical weight in Ruby\n    return 10",
    );
    engine
        .apply_edit(SpokeId::Ruby, &ruby_edited)
        .map_err(|d| d.to_string())?;

    println!("=== 3. Cross-Language Hub Refactor: `Severity::Critical` -> `Severity::Emergency` ===");
    let (snap, renamed_sites) = engine.rename_symbol("Severity::Critical", "Emergency")?;
    let passed_after = snap.test_results.iter().filter(|t| t.passed).count();
    println!(
        "Renamed {} AST sites across all 9 languages | Coverage: {}% | Tests: {}/{} passed | Live Hub VM: {}\n",
        renamed_sites,
        snap.coverage_pct,
        passed_after,
        snap.test_results.len(),
        snap.live_eval.stdout.trim()
    );

    println!("=== 4. Hub AST Mutation Testing & Auto-Test Hardening Across All 9 Languages ===");
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
    println!(
        "--- Updated Rust View (`latencies: &[i64]` slice + `test_mutation_hardened` survived Ruby edit & Hub rename!) ---\n{}",
        hardened_snap.views["rust"]
    );

    println!("=== 5. Differential Execution Across All 9 Engines (Hub VM + rustc + clang++ PCH + swiftc + javac + go + python3 + ruby + node) ===");
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
        "\nParallel wall time: {}ms | Byte-for-byte match across all 9 engines: {}",
        report.wall_time_ms, report.outputs_match
    );
    if !report.outputs_match {
        return Err("runtime outputs diverged".to_string());
    }

    println!("\n=== 6. Property-Based 9-Spoke Lens Fuzzer (25 Synthesized Programs × 9 Spokes) ===");
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

use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;

use crate::autodiff::{AutoDiffReport, NumericalStabilityReport};
use crate::complexity::ComplexityReport;
use crate::concolic::{ConcolicReport, SecurityFlowReport};
use crate::debugger::TimeTravelReport;
use crate::dist_actor::{ActorConcurrencyReport, ModelCheckReport};
use crate::egraph::{EGraphReport, PartialEvalReport};
use crate::engine::{StarEngine, SyncSnapshot};
use crate::fhe_seplogic::{FheCircuitReport, SeparationLogicReport};
use crate::hls_verilog::{GpuSimtReport, HlsRtlReport};
use crate::hub::Diagnostic;
use crate::json::{json_str, parse_flat_json_object};
use crate::lens::SpokeId;
use crate::merge::{MergeReport, SemanticDiffReport};
use crate::microarch::{InstructionScheduleReport, MicroArchReport};
use crate::mutate::MutationReport;
use crate::polyhedral::{PolyhedralReport, TerminationWcetReport};
use crate::quantum_automata::{MinimalDfaReport, QuantumCircuitReport};
use crate::quickcheck::QuickCheckReport;
use crate::refinement_prob::{LiquidRefinementReport, ProbabilisticEntropyReport};
use crate::regalloc::{EscapeAnalysisReport, RegAllocReport};
use crate::repair::RepairReport;
use crate::runner::run_all_spokes;
use crate::samples::{find_sample, SAMPLES};
use crate::ssa::{HoareContractReport, ModuleSsaReport};
use crate::synth::{ModuleCfgReport, SynthReport};
use crate::trace::TraceReport;
use crate::verify::{VerifyReport, VerifyStatus};
use crate::wasm::encode_base64;
use crate::zk_sql::{RelationalSqlReport, ZkCircuitReport};

const UI_HTML: &str = include_str!("ui.html");

pub fn serve_web_studio(port: u16) -> Result<(), String> {
    let addr = format!("127.0.0.1:{}", port);
    let listener = TcpListener::bind(&addr)
        .map_err(|e| format!("failed to bind http://{}: {}", addr, e))?;

    println!("StarLang v2.6 — 13-Spoke Bidirectional Compiler, WebAssembly, Time-Travel, Big-O, QuickCheck, Auto-Repair, PBE Synth, SSA, Hoare WP, Concolic, Taint, E-Graph, Futamura PEval, Polyhedral SIMD, WCET, Chaitin-Briggs RegAlloc, Escape Analysis, Superscalar OoO CPU/Cache/Branch Sim, List Scheduler, Forward/Reverse AutoDiff, Lipschitz Stability, Lamport Vector-Clock Actor Verifier, TLA+ Model Checker, ZK R1CS Prover, Relational SQL Optimizer, Liquid Refinement Types, Probabilistic MCMC/Entropy, Reversible Quantum Circuit Compiler, Minimal DFA Synthesizer, HLS SystemVerilog RTL Compiler, SIMT GPU Kernel Synthesizer, FHE Ring-LWE Blinded Circuit Compiler & Reynolds Separation Logic Studio running at:");
    println!("  -> http://{}", addr);
    println!("Edit Rust, Zig, C11, C++, Swift, Java, Go, Python, Ruby, LuaJIT, Perl 5, TypeScript, or Star S-Expr to sync all 13 spokes, compile native .wasm/.wat, time-travel debug, profile Big-O & gas, run QuickCheck shrinking, synthesize automated program repairs, 3-way AST merge, symbolic safety proofs & 14-engine verification.\n");

    serve_listener(listener)
}

pub fn serve_listener(listener: TcpListener) -> Result<(), String> {
    let default_sample = &SAMPLES[0];
    let engine = StarEngine::from_source(default_sample.initial_spoke, default_sample.source)
        .map_err(|d| d.to_string())?;
    let shared = Arc::new(Mutex::new(engine));

    for stream in listener.incoming().flatten() {
        let shared_clone = Arc::clone(&shared);
        thread::spawn(move || {
            let _ = handle_client(stream, shared_clone);
        });
    }
    Ok(())
}

fn handle_client(mut stream: TcpStream, shared: Arc<Mutex<StarEngine>>) -> std::io::Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut request_line = String::new();
    if reader.read_line(&mut request_line)? == 0 {
        return Ok(());
    }
    let parts: Vec<&str> = request_line.split_whitespace().collect();
    if parts.len() < 2 {
        return Ok(());
    }
    let method = parts[0].to_string();
    let raw_path = parts[1];
    let path = raw_path.split('?').next().unwrap_or(raw_path).to_string();

    let mut content_length: usize = 0;
    loop {
        let mut line = String::new();
        let n = reader.read_line(&mut line)?;
        if n == 0 || line == "\r\n" || line == "\n" {
            break;
        }
        if let Some((k, v)) = line.split_once(':') {
            if k.trim().eq_ignore_ascii_case("content-length") {
                content_length = v.trim().parse::<usize>().unwrap_or(0);
            }
        }
    }

    const MAX_BODY_BYTES: usize = 16 * 1024 * 1024;
    if content_length > MAX_BODY_BYTES {
        return send_response(
            &mut stream,
            413,
            "application/json",
            "{\"ok\":false,\"error\":\"request payload too large\"}",
        );
    }
    let mut body_bytes = vec![0u8; content_length];
    if content_length > 0 {
        reader.read_exact(&mut body_bytes)?;
    }
    let body = String::from_utf8_lossy(&body_bytes).to_string();

    match (method.as_str(), path.as_str()) {
        ("GET", "/") => send_response(&mut stream, 200, "text/html; charset=utf-8", UI_HTML),
        ("GET", "/api/state") => {
            let eng = shared.lock().unwrap();
            let snap = eng.snapshot();
            let payload = format!(
                "{{\"ok\":true,\"snapshot\":{},\"samples\":{}}}",
                snapshot_to_json(&snap),
                samples_to_json()
            );
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/sync") => {
            let parsed = match parse_flat_json_object(&body) {
                Ok(m) => m,
                Err(e) => {
                    let err = format!("{{\"ok\":false,\"error\":{}}}", json_str(&e));
                    return send_response(&mut stream, 400, "application/json", &err);
                }
            };
            let spoke_name = parsed.get("spoke").map(|s| s.as_str()).unwrap_or("");
            let source = parsed.get("source").cloned().unwrap_or_default();
            let Some(spoke) = SpokeId::from_name_or_ext(spoke_name) else {
                return send_response(
                    &mut stream,
                    400,
                    "application/json",
                    "{\"ok\":false,\"error\":\"unknown spoke\"}",
                );
            };

            let mut eng = shared.lock().unwrap();
            match eng.apply_edit(spoke, &source) {
                Ok(snap) => {
                    let payload = format!("{{\"ok\":true,\"snapshot\":{}}}", snapshot_to_json(&snap));
                    send_response(&mut stream, 200, "application/json", &payload)
                }
                Err(diag) => {
                    let payload = format!(
                        "{{\"ok\":false,\"diagnostic\":{}}}",
                        diagnostic_to_json(&diag)
                    );
                    send_response(&mut stream, 200, "application/json", &payload)
                }
            }
        }
        ("POST", "/api/refactor") => {
            let parsed = match parse_flat_json_object(&body) {
                Ok(m) => m,
                Err(e) => {
                    let err = format!("{{\"ok\":false,\"error\":{}}}", json_str(&e));
                    return send_response(&mut stream, 400, "application/json", &err);
                }
            };
            let target = parsed.get("target").map(|s| s.as_str()).unwrap_or("");
            let new_name = parsed.get("new_name").map(|s| s.as_str()).unwrap_or("");

            let mut eng = shared.lock().unwrap();
            match eng.rename_symbol(target, new_name) {
                Ok((snap, count)) => {
                    let payload = format!(
                        "{{\"ok\":true,\"count\":{},\"snapshot\":{}}}",
                        count,
                        snapshot_to_json(&snap)
                    );
                    send_response(&mut stream, 200, "application/json", &payload)
                }
                Err(err_msg) => {
                    let payload = format!("{{\"ok\":false,\"error\":{}}}", json_str(&err_msg));
                    send_response(&mut stream, 200, "application/json", &payload)
                }
            }
        }
        ("POST", "/api/optimize") => {
            let mut eng = shared.lock().unwrap();
            let (snap, rewrites) = eng.optimize();
            let payload = format!(
                "{{\"ok\":true,\"rewrites\":{},\"snapshot\":{}}}",
                rewrites,
                snapshot_to_json(&snap)
            );
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/undo") => {
            let mut eng = shared.lock().unwrap();
            let snap = eng.undo().unwrap_or_else(|| eng.snapshot());
            let payload = format!("{{\"ok\":true,\"snapshot\":{}}}", snapshot_to_json(&snap));
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/redo") => {
            let mut eng = shared.lock().unwrap();
            let snap = eng.redo().unwrap_or_else(|| eng.snapshot());
            let payload = format!("{{\"ok\":true,\"snapshot\":{}}}", snapshot_to_json(&snap));
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/sample") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let id = parsed.get("id").map(|s| s.as_str()).unwrap_or("scores");
            let Some(sample) = find_sample(id) else {
                return send_response(
                    &mut stream,
                    404,
                    "application/json",
                    "{\"ok\":false,\"error\":\"unknown sample\"}",
                );
            };
            let new_eng = match StarEngine::from_source(sample.initial_spoke, sample.source) {
                Ok(e) => e,
                Err(diag) => {
                    let payload = format!(
                        "{{\"ok\":false,\"diagnostic\":{}}}",
                        diagnostic_to_json(&diag)
                    );
                    return send_response(&mut stream, 500, "application/json", &payload);
                }
            };
            let mut eng = shared.lock().unwrap();
            *eng = new_eng;
            let snap = eng.snapshot();
            let payload = format!("{{\"ok\":true,\"snapshot\":{}}}", snapshot_to_json(&snap));
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/trace") => {
            let report = {
                let eng = shared.lock().unwrap();
                eng.trace()
            };
            let payload = trace_to_json(&report);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/verify") => {
            let report = {
                let eng = shared.lock().unwrap();
                eng.verify()
            };
            let payload = verify_to_json(&report);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/mutate") => {
            let report = {
                let eng = shared.lock().unwrap();
                eng.mutate()
            };
            let payload = mutation_to_json(&report);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/harden") => {
            let (snap, hrep) = {
                let mut eng = shared.lock().unwrap();
                eng.harden_tests()
            };
            let payload = format!(
                "{{\"ok\":true,\"added_assertions\":{},\"before_score_pct\":{},\"after_score_pct\":{},\"mutation\":{},\"snapshot\":{}}}",
                hrep.added_assertions,
                hrep.before.score_pct,
                hrep.after.score_pct,
                mutation_to_json(&hrep.after),
                snapshot_to_json(&snap)
            );
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/diff") => {
            let parsed = match parse_flat_json_object(&body) {
                Ok(m) => m,
                Err(e) => {
                    let err = format!("{{\"ok\":false,\"error\":{}}}", json_str(&e));
                    return send_response(&mut stream, 400, "application/json", &err);
                }
            };
            let spoke_name = parsed.get("spoke").map(|s| s.as_str()).unwrap_or("");
            let source = parsed.get("source").cloned().unwrap_or_default();
            let Some(spoke) = SpokeId::from_name_or_ext(spoke_name) else {
                return send_response(
                    &mut stream,
                    400,
                    "application/json",
                    "{\"ok\":false,\"error\":\"unknown spoke\"}",
                );
            };
            let eng = shared.lock().unwrap();
            match eng.diff_with(spoke, &source) {
                Ok(rep) => {
                    let payload = diff_to_json(&rep);
                    send_response(&mut stream, 200, "application/json", &payload)
                }
                Err(diag) => {
                    let payload = format!(
                        "{{\"ok\":false,\"diagnostic\":{}}}",
                        diagnostic_to_json(&diag)
                    );
                    send_response(&mut stream, 200, "application/json", &payload)
                }
            }
        }
        ("POST", "/api/merge") => {
            let parsed = match parse_flat_json_object(&body) {
                Ok(m) => m,
                Err(e) => {
                    let err = format!("{{\"ok\":false,\"error\":{}}}", json_str(&e));
                    return send_response(&mut stream, 400, "application/json", &err);
                }
            };
            let left_name = parsed.get("left_spoke").map(|s| s.as_str()).unwrap_or("");
            let left_src = parsed.get("left_source").cloned().unwrap_or_default();
            let right_name = parsed.get("right_spoke").map(|s| s.as_str()).unwrap_or("");
            let right_src = parsed.get("right_source").cloned().unwrap_or_default();
            let (Some(left_spoke), Some(right_spoke)) = (
                SpokeId::from_name_or_ext(left_name),
                SpokeId::from_name_or_ext(right_name),
            ) else {
                return send_response(
                    &mut stream,
                    400,
                    "application/json",
                    "{\"ok\":false,\"error\":\"unknown left_spoke or right_spoke\"}",
                );
            };

            let mut eng = shared.lock().unwrap();
            match eng.merge_concurrent(left_spoke, &left_src, right_spoke, &right_src) {
                Ok((snap, rep)) => {
                    let payload = merge_to_json(&snap, &rep);
                    send_response(&mut stream, 200, "application/json", &payload)
                }
                Err(diag) => {
                    let payload = format!(
                        "{{\"ok\":false,\"diagnostic\":{}}}",
                        diagnostic_to_json(&diag)
                    );
                    send_response(&mut stream, 200, "application/json", &payload)
                }
            }
        }
        ("POST", "/api/wasm") => {
            let (art_res, run_rep) = {
                let eng = shared.lock().unwrap();
                (eng.compile_wasm(), eng.run_wasm())
            };
            match art_res {
                Ok(art) => {
                    let exports_json: Vec<String> =
                        art.exports.iter().map(|e| json_str(e)).collect();
                    let err_json = run_rep
                        .error
                        .as_deref()
                        .map(json_str)
                        .unwrap_or_else(|| "null".to_string());
                    let payload = format!(
                        "{{\"ok\":true,\"wasm_b64\":{},\"wasm_size_bytes\":{},\"code_bytes\":{},\"data_bytes\":{},\"func_count\":{},\"exports\":[{}],\"wat\":{},\"jit_ok\":{},\"jit_stdout\":{},\"tests_passed\":{},\"tests_total\":{},\"duration_ms\":{},\"error\":{}}}",
                        json_str(&encode_base64(&art.bytes)),
                        art.bytes.len(),
                        art.code_bytes,
                        art.data_bytes,
                        art.func_count,
                        exports_json.join(","),
                        json_str(&art.wat),
                        run_rep.ok,
                        json_str(&run_rep.stdout),
                        run_rep.tests_passed,
                        run_rep.tests_total,
                        run_rep.duration_ms,
                        err_json
                    );
                    send_response(&mut stream, 200, "application/json", &payload)
                }
                Err(err) => {
                    let payload = format!("{{\"ok\":false,\"error\":{}}}", json_str(&err));
                    send_response(&mut stream, 200, "application/json", &payload)
                }
            }
        }
        ("POST", "/api/debug") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let slice_target = parsed.get("slice").map(|s| s.as_str());
            let rep = {
                let eng = shared.lock().unwrap();
                eng.time_travel(slice_target)
            };
            let payload = time_travel_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/complexity") | ("GET", "/api/complexity") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.complexity()
            };
            let payload = complexity_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/quickcheck") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let trials = parsed
                .get("trials")
                .and_then(|s| s.parse::<usize>().ok());
            let rep = {
                let eng = shared.lock().unwrap();
                eng.quickcheck(trials)
            };
            let payload = quickcheck_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/repair") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let inject_demo = parsed
                .get("inject_demo")
                .map(|s| s == "true" || s == "1")
                .unwrap_or(false);
            let (snap, rep, injected_desc) = {
                let mut eng = shared.lock().unwrap();
                eng.repair(inject_demo)
            };
            let payload = repair_to_json(&snap, &rep, injected_desc.as_deref());
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/synth") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let spec_str = parsed.get("spec").map(|s| s.as_str());
            let inject = parsed
                .get("inject")
                .map(|s| s == "true" || s == "1")
                .unwrap_or(false);
            let res = {
                let mut eng = shared.lock().unwrap();
                eng.synthesize(spec_str, inject)
            };
            match res {
                Ok((rep, snap)) => {
                    let payload = synth_to_json(&rep, snap.as_ref());
                    send_response(&mut stream, 200, "application/json", &payload)
                }
                Err(err) => {
                    let payload = format!("{{\"ok\":false,\"error\":{}}}", json_str(&err));
                    send_response(&mut stream, 400, "application/json", &payload)
                }
            }
        }
        ("POST", "/api/cfg") | ("GET", "/api/cfg") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.cfg()
            };
            let payload = cfg_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/ssa") | ("GET", "/api/ssa") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.ssa()
            };
            let payload = ssa_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/contracts") | ("GET", "/api/contracts") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.contracts()
            };
            let payload = contracts_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/concolic") | ("GET", "/api/concolic") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let inject = parsed
                .get("inject")
                .map(|s| s == "true" || s == "1")
                .unwrap_or(false);
            let (rep, snap) = {
                let mut eng = shared.lock().unwrap();
                eng.concolic(inject)
            };
            let payload = concolic_to_json(&rep, snap.as_ref());
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/security") | ("GET", "/api/security") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.security_flow()
            };
            let payload = security_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/egraph") | ("GET", "/api/egraph") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let apply = parsed
                .get("apply")
                .map(|s| s == "true" || s == "1")
                .unwrap_or(false);
            let (rep, snap) = {
                let mut eng = shared.lock().unwrap();
                eng.egraph(apply)
            };
            let payload = egraph_to_json(&rep, snap.as_ref());
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/peval") | ("GET", "/api/peval") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let apply = parsed
                .get("apply")
                .map(|s| s == "true" || s == "1")
                .unwrap_or(false);
            let (rep, snap) = {
                let mut eng = shared.lock().unwrap();
                eng.partial_eval(apply)
            };
            let payload = peval_to_json(&rep, snap.as_ref());
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/polyhedral") | ("GET", "/api/polyhedral") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.polyhedral()
            };
            let payload = polyhedral_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/wcet") | ("GET", "/api/wcet") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.termination_wcet()
            };
            let payload = wcet_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/regalloc") | ("GET", "/api/regalloc") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let k = parsed
                .get("k")
                .and_then(|s| s.parse::<usize>().ok());
            let rep = {
                let eng = shared.lock().unwrap();
                eng.regalloc(k)
            };
            let payload = regalloc_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/escape") | ("GET", "/api/escape") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.escape_analysis()
            };
            let payload = escape_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/microarch") | ("GET", "/api/microarch") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.microarch()
            };
            let payload = microarch_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/schedule") | ("GET", "/api/schedule") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.schedule_instructions()
            };
            let payload = schedule_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/autodiff") | ("GET", "/api/autodiff") => {
            let parsed = parse_flat_json_object(&body).unwrap_or_default();
            let inject = parsed
                .get("inject")
                .map(|s| s == "true" || s == "1")
                .unwrap_or(false);
            let (rep, snap_opt) = {
                let mut eng = shared.lock().unwrap();
                eng.autodiff(inject)
            };
            let payload = autodiff_to_json(&rep, snap_opt.as_ref());
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/stability") | ("GET", "/api/stability") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.numerical_stability()
            };
            let payload = stability_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/actors") | ("GET", "/api/actors") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.actors()
            };
            let payload = actors_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/modelcheck") | ("GET", "/api/modelcheck") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.model_check()
            };
            let payload = modelcheck_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/zk") | ("GET", "/api/zk") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.zk_r1cs()
            };
            let payload = zk_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/sql") | ("GET", "/api/sql") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.relational_sql()
            };
            let payload = sql_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/refinement") | ("GET", "/api/refinement") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.liquid_refinements()
            };
            let payload = refinement_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/prob") | ("GET", "/api/prob") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.probabilistic_entropy()
            };
            let payload = prob_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/quantum") | ("GET", "/api/quantum") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.quantum_circuit()
            };
            let payload = quantum_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/automata") | ("GET", "/api/automata") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.minimal_dfa()
            };
            let payload = automata_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/hls") | ("GET", "/api/hls") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.hls_rtl()
            };
            let payload = hls_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/gpu") | ("GET", "/api/gpu") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.gpu_simt()
            };
            let payload = gpu_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/fhe") | ("GET", "/api/fhe") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.fhe_circuit()
            };
            let payload = fhe_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/seplogic") | ("GET", "/api/seplogic") => {
            let rep = {
                let eng = shared.lock().unwrap();
                eng.separation_logic()
            };
            let payload = seplogic_to_json(&rep);
            send_response(&mut stream, 200, "application/json", &payload)
        }
        ("POST", "/api/run") => {
            let report = {
                let eng = shared.lock().unwrap();
                run_all_spokes(&eng)
            };
            let results_json: Vec<String> = report
                .results
                .iter()
                .map(|r| {
                    format!(
                        "{{\"language\":{},\"ok\":{},\"stdout\":{},\"stderr\":{},\"duration_ms\":{}}}",
                        json_str(r.language),
                        r.ok,
                        json_str(&r.stdout),
                        json_str(&r.stderr),
                        r.duration_ms
                    )
                })
                .collect();
            let payload = format!(
                "{{\"ok\":true,\"all_succeeded\":{},\"outputs_match\":{},\"wall_time_ms\":{},\"results\":[{}]}}",
                report.all_succeeded,
                report.outputs_match,
                report.wall_time_ms,
                results_json.join(",")
            );
            send_response(&mut stream, 200, "application/json", &payload)
        }
        _ => send_response(&mut stream, 404, "text/plain", "Not Found"),
    }
}

fn snapshot_to_json(snap: &SyncSnapshot) -> String {
    let views_entries: Vec<String> = snap
        .views
        .iter()
        .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
        .collect();
    let badges_entries: Vec<String> = snap.metadata_badges.iter().map(|b| json_str(b)).collect();
    let sem_entries: Vec<String> = snap
        .semantic_diagnostics
        .iter()
        .map(|d| {
            format!(
                "{{\"node_id\":{},\"context\":{},\"message\":{}}}",
                d.node_id,
                json_str(&d.context),
                json_str(&d.message)
            )
        })
        .collect();
    let sym_entries: Vec<String> = snap
        .symbols
        .iter()
        .map(|s| {
            format!(
                "{{\"spec\":{},\"label\":{},\"current_name\":{}}}",
                json_str(&s.spec),
                json_str(&s.label),
                json_str(&s.current_name)
            )
        })
        .collect();
    let live_err = snap
        .live_eval
        .error
        .as_deref()
        .map(json_str)
        .unwrap_or_else(|| "null".to_string());
    let live_json = format!(
        "{{\"ok\":{},\"stdout\":{},\"steps\":{},\"error\":{}}}",
        snap.live_eval.ok,
        json_str(&snap.live_eval.stdout),
        snap.live_eval.steps,
        live_err
    );
    let test_entries: Vec<String> = snap
        .test_results
        .iter()
        .map(|tr| {
            let err_json = tr
                .error
                .as_deref()
                .map(json_str)
                .unwrap_or_else(|| "null".to_string());
            format!(
                "{{\"name\":{},\"passed\":{},\"steps\":{},\"error\":{}}}",
                json_str(&tr.name),
                tr.passed,
                tr.steps,
                err_json
            )
        })
        .collect();

    format!(
        "{{\"revision\":{},\"active_spoke\":{},\"node_count\":{},\"can_undo\":{},\"can_redo\":{},\"coverage_pct\":{},\"covered_stmts\":{},\"total_stmts\":{},\"safety_proven\":{},\"safety_total\":{},\"safety_refuted\":{},\"unreachable_count\":{},\"metadata_badges\":[{}],\"semantic_diagnostics\":[{}],\"symbols\":[{}],\"live_eval\":{},\"test_results\":[{}],\"views\":{{{}}}}}",
        snap.revision,
        json_str(snap.active_spoke.as_str()),
        snap.node_count,
        snap.can_undo,
        snap.can_redo,
        snap.coverage_pct,
        snap.covered_stmts,
        snap.total_stmts,
        snap.safety_proven,
        snap.safety_total,
        snap.safety_refuted,
        snap.unreachable_count,
        badges_entries.join(","),
        sem_entries.join(","),
        sym_entries.join(","),
        live_json,
        test_entries.join(","),
        views_entries.join(",")
    )
}

fn trace_to_json(report: &TraceReport) -> String {
    let err_json = report
        .error
        .as_deref()
        .map(json_str)
        .unwrap_or_else(|| "null".to_string());
    let uncov_entries: Vec<String> = report
        .uncovered
        .iter()
        .map(|u| {
            format!(
                "{{\"node_id\":{},\"func\":{},\"summary\":{}}}",
                u.node_id,
                json_str(&u.func),
                json_str(&u.summary)
            )
        })
        .collect();
    let hotspot_entries: Vec<String> = report
        .hotspots
        .iter()
        .map(|h| {
            format!(
                "{{\"name\":{},\"calls\":{},\"total_steps\":{}}}",
                json_str(&h.name),
                h.calls,
                h.total_steps
            )
        })
        .collect();
    let call_entries: Vec<String> = report
        .call_trace
        .iter()
        .map(|c| {
            format!(
                "{{\"depth\":{},\"callee\":{},\"args\":{},\"result\":{},\"steps\":{}}}",
                c.depth,
                json_str(&c.callee),
                json_str(&c.args),
                json_str(&c.result),
                c.steps
            )
        })
        .collect();

    format!(
        "{{\"ok\":{},\"coverage_pct\":{},\"covered_stmts\":{},\"total_stmts\":{},\"error\":{},\"uncovered\":[{}],\"hotspots\":[{}],\"call_trace\":[{}]}}",
        report.ok,
        report.coverage_pct,
        report.covered_stmts,
        report.total_stmts,
        err_json,
        uncov_entries.join(","),
        hotspot_entries.join(","),
        call_entries.join(",")
    )
}

fn mutation_to_json(report: &MutationReport) -> String {
    let items: Vec<String> = report
        .outcomes
        .iter()
        .map(|m| {
            let kb = m
                .killed_by
                .as_deref()
                .map(json_str)
                .unwrap_or_else(|| "null".to_string());
            format!(
                "{{\"id\":{},\"func\":{},\"description\":{},\"killed\":{},\"killed_by\":{}}}",
                m.id,
                json_str(&m.func),
                json_str(&m.description),
                m.killed,
                kb
            )
        })
        .collect();
    format!(
        "{{\"ok\":true,\"total_mutants\":{},\"killed\":{},\"survived\":{},\"score_pct\":{},\"elapsed_ms\":{},\"outcomes\":[{}]}}",
        report.total_mutants,
        report.killed,
        report.survived,
        report.score_pct,
        report.elapsed_ms,
        items.join(",")
    )
}

fn verify_to_json(report: &VerifyReport) -> String {
    let ob_entries: Vec<String> = report
        .obligations
        .iter()
        .map(|ob| {
            let (witness_json, err_json) = match &ob.status {
                VerifyStatus::Refuted {
                    witness_call,
                    runtime_error,
                } => (json_str(witness_call), json_str(runtime_error)),
                _ => ("null".to_string(), "null".to_string()),
            };
            format!(
                "{{\"id\":{},\"func\":{},\"kind\":{},\"label\":{},\"expr\":{},\"status\":{},\"note\":{},\"witness_call\":{},\"runtime_error\":{}}}",
                ob.id,
                json_str(&ob.func),
                json_str(ob.kind.as_str()),
                json_str(ob.kind.label()),
                json_str(&ob.expr_summary),
                json_str(ob.status.as_str()),
                json_str(&ob.proof_note),
                witness_json,
                err_json
            )
        })
        .collect();

    let dead_entries: Vec<String> = report
        .unreachable_branches
        .iter()
        .map(|u| {
            format!(
                "{{\"func\":{},\"stmt_id\":{},\"branch\":{},\"cond\":{},\"reason\":{}}}",
                json_str(&u.func),
                u.stmt_id,
                json_str(u.branch),
                json_str(&u.cond_summary),
                json_str(&u.reason)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"all_safe\":{},\"total_obligations\":{},\"proven_safe\":{},\"refuted\":{},\"warnings\":{},\"elapsed_ms\":{},\"obligations\":[{}],\"unreachable_branches\":[{}]}}",
        report.all_safe(),
        report.total_obligations,
        report.proven_safe,
        report.refuted,
        report.warnings,
        report.elapsed_ms,
        ob_entries.join(","),
        dead_entries.join(",")
    )
}

fn diff_to_json(report: &SemanticDiffReport) -> String {
    let entries: Vec<String> = report
        .deltas
        .iter()
        .map(|d| {
            format!(
                "{{\"kind\":{},\"scope\":{},\"summary\":{}}}",
                json_str(d.kind),
                json_str(&d.scope),
                json_str(&d.summary)
            )
        })
        .collect();
    format!(
        "{{\"ok\":true,\"identical\":{},\"deltas\":[{}]}}",
        report.identical,
        entries.join(",")
    )
}

fn merge_to_json(snap: &SyncSnapshot, report: &MergeReport) -> String {
    let applied: Vec<String> = report
        .applied_changes
        .iter()
        .map(|a| {
            format!(
                "{{\"spoke\":{},\"scope\":{},\"summary\":{}}}",
                json_str(a.spoke.display_name()),
                json_str(&a.scope),
                json_str(&a.summary)
            )
        })
        .collect();
    let conflicts: Vec<String> = report
        .conflicts
        .iter()
        .map(|c| {
            format!(
                "{{\"node_id\":{},\"scope\":{},\"description\":{},\"base_summary\":{},\"left_spoke\":{},\"left_summary\":{},\"right_spoke\":{},\"right_summary\":{}}}",
                c.node_id,
                json_str(&c.scope),
                json_str(&c.description),
                json_str(&c.base_summary),
                json_str(c.left_spoke.display_name()),
                json_str(&c.left_summary),
                json_str(c.right_spoke.display_name()),
                json_str(&c.right_summary)
            )
        })
        .collect();
    format!(
        "{{\"ok\":true,\"clean\":{},\"applied_changes\":[{}],\"conflicts\":[{}],\"snapshot\":{}}}",
        report.clean,
        applied.join(","),
        conflicts.join(","),
        snapshot_to_json(snap)
    )
}

fn diagnostic_to_json(d: &Diagnostic) -> String {
    format!(
        "{{\"language\":{},\"message\":{},\"line\":{},\"col\":{}}}",
        json_str(&d.language),
        json_str(&d.message),
        d.line,
        d.col
    )
}

fn time_travel_to_json(rep: &TimeTravelReport) -> String {
    let fault_json = rep
        .fault
        .as_deref()
        .map(json_str)
        .unwrap_or_else(|| "null".to_string());
    let steps_json: Vec<String> = rep
        .steps
        .iter()
        .map(|s| {
            let deltas: Vec<String> = s
                .deltas
                .iter()
                .map(|d| {
                    let b = d
                        .before
                        .as_deref()
                        .map(json_str)
                        .unwrap_or_else(|| "null".to_string());
                    format!(
                        "{{\"name\":{},\"before\":{},\"after\":{}}}",
                        json_str(&d.name),
                        b,
                        json_str(&d.after)
                    )
                })
                .collect();
            let locals: Vec<String> = s
                .locals
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            let stack: Vec<String> = s.call_stack.iter().map(|f| json_str(f)).collect();
            let lines: Vec<String> = s
                .spoke_lines
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), v))
                .collect();
            let reads: Vec<String> = s.read_vars.iter().map(|r| json_str(r)).collect();
            let written = s
                .written_var
                .as_deref()
                .map(json_str)
                .unwrap_or_else(|| "null".to_string());
            let ctrl = s
                .control_parent_step
                .map(|idx| idx.to_string())
                .unwrap_or_else(|| "null".to_string());
            format!(
                "{{\"step_index\":{},\"stmt_id\":{},\"func\":{},\"depth\":{},\"kind\":{},\"summary\":{},\"deltas\":[{}],\"locals\":{{{}}},\"call_stack\":[{}],\"stdout_so_far\":{},\"spoke_lines\":{{{}}},\"read_vars\":[{}],\"written_var\":{},\"control_parent_step\":{}}}",
                s.step_index,
                s.stmt_id,
                json_str(&s.func),
                s.depth,
                json_str(&s.kind),
                json_str(&s.summary),
                deltas.join(","),
                locals.join(","),
                stack.join(","),
                json_str(&s.stdout_so_far),
                lines.join(","),
                reads.join(","),
                written,
                ctrl
            )
        })
        .collect();

    let slice_json = if let Some(sl) = &rep.slice {
        let s_steps: Vec<String> = sl.slice_steps.iter().map(|i| i.to_string()).collect();
        let expl: Vec<String> = sl.explanation.iter().map(|e| json_str(e)).collect();
        format!(
            "{{\"target\":{},\"anchor_step\":{},\"slice_steps\":[{}],\"explanation\":[{}]}}",
            json_str(&sl.target),
            sl.anchor_step,
            s_steps.join(","),
            expl.join(",")
        )
    } else {
        "null".to_string()
    };

    format!(
        "{{\"ok\":true,\"trace_ok\":{},\"fault\":{},\"total_steps\":{},\"max_depth\":{},\"final_stdout\":{},\"steps\":[{}],\"slice\":{}}}",
        rep.ok,
        fault_json,
        rep.total_steps,
        rep.max_depth,
        json_str(&rep.final_stdout),
        steps_json.join(","),
        slice_json
    )
}

fn complexity_to_json(rep: &ComplexityReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let pts: Vec<String> = f
                .scaling_points
                .iter()
                .map(|p| {
                    format!(
                        "{{\"n\":{},\"steps\":{},\"compute_gas\":{},\"memory_gas\":{},\"alloc_gas\":{},\"branch_gas\":{},\"total_gas\":{}}}",
                        p.n,
                        p.steps,
                        p.compute_gas,
                        p.memory_gas,
                        p.alloc_gas,
                        p.branch_gas,
                        p.total_gas
                    )
                })
                .collect();
            format!(
                "{{\"name\":{},\"signature\":{},\"cyclomatic_complexity\":{},\"max_loop_depth\":{},\"is_recursive\":{},\"heap_alloc_sites\":{},\"static_big_o\":{},\"empirical_big_o\":{},\"growth_ratio\":{:.2},\"scaling_points\":[{}]}}",
                json_str(&f.name),
                json_str(&f.signature),
                f.cyclomatic_complexity,
                f.max_loop_depth,
                f.is_recursive,
                f.heap_alloc_sites,
                json_str(&f.static_big_o),
                json_str(&f.empirical_big_o),
                f.growth_ratio,
                pts.join(",")
            )
        })
        .collect();

    let spokes_json: Vec<String> = rep
        .spoke_metrics
        .iter()
        .map(|m| {
            format!(
                "{{\"spoke\":{},\"display_name\":{},\"total_lines\":{},\"logic_lines\":{},\"bytes\":{},\"tokens\":{}}}",
                json_str(&m.spoke),
                json_str(&m.display_name),
                m.total_lines,
                m.logic_lines,
                m.bytes,
                m.tokens
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"max_cyclomatic\":{},\"max_loop_depth\":{},\"dominant_big_o\":{},\"wasm_bytes\":{},\"module_gas\":{{\"total_steps\":{},\"compute_gas\":{},\"memory_gas\":{},\"alloc_gas\":{},\"branch_gas\":{},\"total_gas\":{}}},\"functions\":[{}],\"spoke_metrics\":[{}]}}",
        rep.total_functions,
        rep.max_cyclomatic,
        rep.max_loop_depth,
        json_str(&rep.dominant_big_o),
        rep.wasm_bytes,
        rep.module_gas.total_steps,
        rep.module_gas.compute_gas,
        rep.module_gas.memory_gas,
        rep.module_gas.alloc_gas,
        rep.module_gas.branch_gas,
        rep.module_gas.total_gas,
        fns_json.join(","),
        spokes_json.join(",")
    )
}

fn quickcheck_to_json(rep: &QuickCheckReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let invs: Vec<String> = f.discovered_invariants.iter().map(|i| json_str(i)).collect();
            let ce_json = if let Some(ce) = &f.counterexample {
                let repros: Vec<String> = ce
                    .repro_by_spoke
                    .iter()
                    .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                    .collect();
                format!(
                    "{{\"fn_name\":{},\"original_args\":{},\"minimized_args\":{},\"shrink_steps\":{},\"fault\":{},\"repro_by_spoke\":{{{}}}}}",
                    json_str(&ce.fn_name),
                    json_str(&ce.original_args),
                    json_str(&ce.minimized_args),
                    ce.shrink_steps,
                    json_str(&ce.fault),
                    repros.join(",")
                )
            } else {
                "null".to_string()
            };
            format!(
                "{{\"name\":{},\"signature\":{},\"trials_run\":{},\"passed_trials\":{},\"contract_safe\":{},\"optimizer_equivalent\":{},\"deterministic\":{},\"discovered_invariants\":[{}],\"counterexample\":{}}}",
                json_str(&f.name),
                json_str(&f.signature),
                f.trials_run,
                f.passed_trials,
                f.contract_safe,
                f.optimizer_equivalent,
                f.deterministic,
                invs.join(","),
                ce_json
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"all_passed\":{},\"trials_per_fn\":{},\"total_functions\":{},\"total_trials\":{},\"optimizer_checks\":{},\"total_invariants\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.all_passed,
        rep.trials_per_fn,
        rep.total_functions,
        rep.total_trials,
        rep.optimizer_checks,
        rep.total_invariants,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn repair_to_json(
    snap: &SyncSnapshot,
    rep: &RepairReport,
    injected_desc: Option<&str>,
) -> String {
    let inj_json = injected_desc
        .map(json_str)
        .unwrap_or_else(|| "null".to_string());
    let faults_json: Vec<String> = rep
        .faults
        .iter()
        .map(|f| {
            let lines: Vec<String> = f
                .spoke_lines
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), v))
                .collect();
            format!(
                "{{\"stmt_id\":{},\"func\":{},\"symptom\":{},\"spoke_lines\":{{{}}}}}",
                f.stmt_id,
                json_str(&f.func),
                json_str(&f.symptom),
                lines.join(",")
            )
        })
        .collect();

    let patch_json = if let Some(p) = &rep.patch {
        let lines: Vec<String> = p
            .spoke_lines
            .iter()
            .map(|(k, v)| format!("{}:{}", json_str(k), v))
            .collect();
        let diffs: Vec<String> = p
            .diffs_by_spoke
            .iter()
            .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
            .collect();
        format!(
            "{{\"stmt_id\":{},\"func\":{},\"kind\":{},\"before_summary\":{},\"after_summary\":{},\"spoke_lines\":{{{}}},\"diffs_by_spoke\":{{{}}}}}",
            p.stmt_id,
            json_str(&p.func),
            json_str(&p.kind),
            json_str(&p.before_summary),
            json_str(&p.after_summary),
            lines.join(","),
            diffs.join(",")
        )
    } else {
        "null".to_string()
    };

    format!(
        "{{\"ok\":true,\"already_healthy\":{},\"repaired\":{},\"injected_bug\":{},\"candidates_evaluated\":{},\"tests_passed_before\":{},\"tests_total\":{},\"tests_passed_after\":{},\"safety_refuted_before\":{},\"safety_refuted_after\":{},\"quickcheck_passed\":{},\"elapsed_ms\":{},\"faults\":[{}],\"patch\":{},\"snapshot\":{}}}",
        rep.already_healthy,
        rep.repaired,
        inj_json,
        rep.candidates_evaluated,
        rep.tests_passed_before,
        rep.tests_total,
        rep.tests_passed_after,
        rep.safety_refuted_before,
        rep.safety_refuted_after,
        rep.quickcheck_passed,
        rep.elapsed_ms,
        faults_json.join(","),
        patch_json,
        snapshot_to_json(snap)
    )
}

fn synth_to_json(rep: &SynthReport, snap: Option<&SyncSnapshot>) -> String {
    let views_entries: Vec<String> = rep
        .views_by_spoke
        .iter()
        .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
        .collect();
    let snap_json = snap
        .map(snapshot_to_json)
        .unwrap_or_else(|| "null".to_string());
    format!(
        "{{\"ok\":true,\"synthesized\":{},\"fn_name\":{},\"signature\":{},\"examples_count\":{},\"candidates_enumerated\":{},\"observationally_unique\":{},\"pruned_equivalents\":{},\"synthesized_summary\":{},\"test_passed\":{},\"safety_proven\":{},\"elapsed_ms\":{},\"views\":{{{}}},\"snapshot\":{}}}",
        rep.ok,
        json_str(&rep.fn_name),
        json_str(&rep.signature),
        rep.examples_count,
        rep.candidates_explored,
        rep.candidates_explored.saturating_sub(rep.pruned_by_obs_equiv),
        rep.pruned_by_obs_equiv,
        json_str(&rep.program_summary),
        rep.tests_passed,
        rep.safety_proven,
        rep.elapsed_ms,
        views_entries.join(","),
        snap_json
    )
}

fn cfg_to_json(rep: &ModuleCfgReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let bbs: Vec<String> = f
                .blocks
                .iter()
                .map(|b| {
                    let stmts: Vec<String> = b.stmts.iter().map(|s| json_str(s)).collect();
                    let succs: Vec<String> = b
                        .successors
                        .iter()
                        .map(|(dst, _)| dst.to_string())
                        .collect();
                    let preds: Vec<String> = b.predecessors.iter().map(|i| i.to_string()).collect();
                    let doms: Vec<String> = b.dominators.iter().map(|i| i.to_string()).collect();
                    format!(
                        "{{\"id\":{},\"label\":{},\"stmts\":[{}],\"terminator\":{},\"successors\":[{}],\"predecessors\":[{}],\"dominators\":[{}]}}",
                        b.id,
                        json_str(&b.label),
                        stmts.join(","),
                        json_str(&b.kind),
                        succs.join(","),
                        preds.join(","),
                        doms.join(",")
                    )
                })
                .collect();
            let back_edges: Vec<String> = f
                .back_edges
                .iter()
                .map(|(u, v)| format!("[{},{}]", u, v))
                .collect();
            format!(
                "{{\"name\":{},\"signature\":{},\"natural_loop_count\":{},\"back_edges\":[{}],\"blocks\":[{}],\"mermaid\":{},\"graphviz_dot\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.natural_loops,
                back_edges.join(","),
                bbs.join(","),
                json_str(&f.mermaid),
                json_str(&f.dot)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_blocks\":{},\"total_edges\":{},\"total_natural_loops\":{},\"functions\":[{}]}}",
        rep.total_blocks,
        rep.total_edges,
        rep.total_natural_loops,
        fns_json.join(",")
    )
}

fn ssa_to_json(rep: &ModuleSsaReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let chains: Vec<String> = f
                .def_use_chains
                .iter()
                .map(|c| {
                    let uses: Vec<String> = c
                        .uses
                        .iter()
                        .map(|(b, u)| format!("[{},{}]", b, json_str(u)))
                        .collect();
                    format!(
                        "{{\"ssa_var\":{},\"base_var\":{},\"def_block\":{},\"def_kind\":{},\"uses\":[{}],\"is_dead_store\":{}}}",
                        json_str(&c.ssa_var),
                        json_str(&c.base_var),
                        c.def_block,
                        json_str(&c.def_kind),
                        uses.join(","),
                        c.is_dead_store
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"block_count\":{},\"phi_count\":{},\"total_ssa_defs\":{},\"dead_store_count\":{},\"def_use_chains\":[{}],\"ssa_listing\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.block_count,
                f.phi_count,
                f.total_ssa_defs,
                f.dead_store_count,
                chains.join(","),
                json_str(&f.ssa_listing)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_blocks\":{},\"total_phi_nodes\":{},\"total_ssa_defs\":{},\"total_dead_stores\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_blocks,
        rep.total_phi_nodes,
        rep.total_ssa_defs,
        rep.total_dead_stores,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn contracts_to_json(rep: &HoareContractReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let reqs: Vec<String> = f.requires.iter().map(|s| json_str(s)).collect();
            let invs: Vec<String> = f.loop_invariants.iter().map(|s| json_str(s)).collect();
            let enss: Vec<String> = f.ensures.iter().map(|s| json_str(s)).collect();
            let anns: Vec<String> = f
                .annotated_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"requires\":[{}],\"loop_invariants\":[{}],\"ensures\":[{}],\"vcs_total\":{},\"vcs_proven\":{},\"verified\":{},\"annotated_by_spoke\":{{{}}}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                reqs.join(","),
                invs.join(","),
                enss.join(","),
                f.vcs_total,
                f.vcs_proven,
                f.verified,
                anns.join(",")
            )
        })
        .collect();

    let vcs_json: Vec<String> = rep
        .verification_conditions
        .iter()
        .map(|vc| {
            format!(
                "{{\"id\":{},\"fn_name\":{},\"kind\":{},\"obligation\":{},\"wp_formula\":{},\"proven\":{},\"proof_note\":{}}}",
                vc.id,
                json_str(&vc.fn_name),
                json_str(&vc.kind),
                json_str(&vc.obligation),
                json_str(&vc.wp_formula),
                vc.proven,
                json_str(&vc.proof_note)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"all_verified\":{},\"total_functions\":{},\"total_requires\":{},\"total_invariants\":{},\"total_ensures\":{},\"total_vcs\":{},\"proven_vcs\":{},\"elapsed_ms\":{},\"functions\":[{}],\"verification_conditions\":[{}]}}",
        rep.all_verified,
        rep.total_functions,
        rep.total_requires,
        rep.total_invariants,
        rep.total_ensures,
        rep.total_vcs,
        rep.proven_vcs,
        rep.elapsed_ms,
        fns_json.join(","),
        vcs_json.join(",")
    )
}

fn concolic_to_json(rep: &ConcolicReport, snap: Option<&SyncSnapshot>) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let paths: Vec<String> = f
                .paths
                .iter()
                .map(|p| {
                    let brs: Vec<String> = p.branches_taken.iter().map(|b| json_str(b)).collect();
                    format!(
                        "{{\"path_id\":{},\"signature_key\":{},\"path_condition\":{},\"input_args\":{},\"output_val\":{},\"branches_taken\":[{}],\"steps\":{}}}",
                        p.path_id,
                        json_str(&p.signature_key),
                        json_str(&p.path_condition),
                        json_str(&p.input_args),
                        json_str(&p.output_val),
                        brs.join(","),
                        p.steps
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"total_branches\":{},\"covered_branches\":{},\"branch_coverage_pct\":{},\"paths_discovered\":{},\"synthesized_assertions\":{},\"paths\":[{}]}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.total_branches,
                f.covered_branches,
                f.branch_coverage_pct,
                f.paths_discovered,
                f.synthesized_assertions,
                paths.join(",")
            )
        })
        .collect();

    let snap_json = snap
        .map(snapshot_to_json)
        .unwrap_or_else(|| "null".to_string());

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_paths\":{},\"total_branches\":{},\"covered_branches\":{},\"branch_coverage_pct\":{},\"synthesized_tests_count\":{},\"synthesized_assertions_count\":{},\"all_synthesized_tests_pass\":{},\"elapsed_ms\":{},\"functions\":[{}],\"snapshot\":{}}}",
        rep.total_functions,
        rep.total_paths,
        rep.total_branches,
        rep.covered_branches,
        rep.branch_coverage_pct,
        rep.synthesized_tests_count,
        rep.synthesized_assertions_count,
        rep.all_synthesized_tests_pass,
        rep.elapsed_ms,
        fns_json.join(","),
        snap_json
    )
}

fn security_to_json(rep: &SecurityFlowReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let untrusted: Vec<String> = f.untrusted_params.iter().map(|s| json_str(s)).collect();
            let confid: Vec<String> = f.confidential_params.iter().map(|s| json_str(s)).collect();
            let edges: Vec<String> = f
                .flow_edges
                .iter()
                .map(|e| {
                    format!(
                        "{{\"from_var\":{},\"to_target\":{},\"flow_kind\":{},\"taint_label\":{},\"stmt_id\":{}}}",
                        json_str(&e.from_var),
                        json_str(&e.to_target),
                        json_str(&e.flow_kind),
                        json_str(&e.taint_label),
                        e.stmt_id
                    )
                })
                .collect();
            let sinks: Vec<String> = f
                .sink_audits
                .iter()
                .map(|s| {
                    format!(
                        "{{\"stmt_id\":{},\"func\":{},\"sink_kind\":{},\"expr_summary\":{},\"taint_state\":{},\"safe\":{},\"note\":{}}}",
                        s.stmt_id,
                        json_str(&s.func),
                        json_str(&s.sink_kind),
                        json_str(&s.expr_summary),
                        json_str(&s.taint_state),
                        s.safe,
                        json_str(&s.note)
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"untrusted_params\":[{}],\"confidential_params\":[{}],\"sanitizers_applied\":{},\"explicit_flows\":{},\"implicit_control_flows\":{},\"constant_time_clean\":{},\"timing_note\":{},\"flow_edges\":[{}],\"sink_audits\":[{}]}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                untrusted.join(","),
                confid.join(","),
                f.sanitizers_applied,
                f.explicit_flows,
                f.implicit_control_flows,
                f.constant_time_clean,
                json_str(&f.timing_note),
                edges.join(","),
                sinks.join(",")
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"all_sinks_safe\":{},\"total_functions\":{},\"total_flows\":{},\"total_sanitizers\":{},\"total_sinks\":{},\"safe_sinks\":{},\"unsanitized_sinks\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.all_sinks_safe,
        rep.total_functions,
        rep.total_flows,
        rep.total_sanitizers,
        rep.total_sinks,
        rep.safe_sinks,
        rep.unsanitized_sinks,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn egraph_to_json(rep: &EGraphReport, snap: Option<&SyncSnapshot>) -> String {
    let rules_json: Vec<String> = rep
        .rules_fired
        .iter()
        .map(|(k, v)| format!("{}:{}", json_str(k), v))
        .collect();
    let rewrites_json: Vec<String> = rep
        .rewrites
        .iter()
        .map(|w| {
            format!(
                "{{\"scope\":{},\"eclass_id\":{},\"before_expr\":{},\"after_expr\":{},\"cost_before\":{},\"cost_after\":{},\"class_size\":{}}}",
                json_str(&w.scope),
                w.eclass_id,
                json_str(&w.before_expr),
                json_str(&w.after_expr),
                w.cost_before,
                w.cost_after,
                w.class_size
            )
        })
        .collect();
    let views_json: Vec<String> = rep
        .views_by_spoke
        .iter()
        .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
        .collect();
    let snap_json = snap
        .map(snapshot_to_json)
        .unwrap_or_else(|| "null".to_string());

    format!(
        "{{\"ok\":true,\"total_eclasses\":{},\"total_enodes\":{},\"total_unions\":{},\"saturation_iterations\":{},\"expressions_optimized\":{},\"dead_branches_pruned\":{},\"cost_before\":{},\"cost_after\":{},\"gas_saved\":{},\"translation_validated\":{},\"rules_fired\":{{{}}},\"rewrites\":[{}],\"mermaid\":{},\"views_by_spoke\":{{{}}},\"elapsed_ms\":{},\"snapshot\":{}}}",
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
        rules_json.join(","),
        rewrites_json.join(","),
        json_str(&rep.mermaid),
        views_json.join(","),
        rep.elapsed_ms,
        snap_json
    )
}

fn peval_to_json(rep: &PartialEvalReport, snap: Option<&SyncSnapshot>) -> String {
    let specs_json: Vec<String> = rep
        .specializations
        .iter()
        .map(|s| {
            format!(
                "{{\"caller\":{},\"callee\":{},\"specialized_name\":{},\"static_bindings\":{},\"summary\":{}}}",
                json_str(&s.caller),
                json_str(&s.callee),
                json_str(&s.specialized_name),
                json_str(&s.static_bindings),
                json_str(&s.summary)
            )
        })
        .collect();
    let views_json: Vec<String> = rep
        .views_by_spoke
        .iter()
        .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
        .collect();
    let snap_json = snap
        .map(snapshot_to_json)
        .unwrap_or_else(|| "null".to_string());

    format!(
        "{{\"ok\":true,\"specialized_calls\":{},\"residual_functions_synthesized\":{},\"static_branches_folded\":{},\"loops_unrolled\":{},\"egraph_rewrites\":{},\"nodes_before\":{},\"nodes_after\":{},\"vm_steps_before\":{},\"vm_steps_after\":{},\"gas_before\":{},\"gas_after\":{},\"translation_validated\":{},\"stdout_before\":{},\"stdout_after\":{},\"tests_passed\":{},\"tests_total\":{},\"specializations\":[{}],\"views_by_spoke\":{{{}}},\"elapsed_ms\":{},\"snapshot\":{}}}",
        rep.specialized_calls,
        rep.residual_functions_synthesized,
        rep.static_branches_folded,
        rep.loops_unrolled,
        rep.egraph_rewrites,
        rep.nodes_before,
        rep.nodes_after,
        rep.vm_steps_before,
        rep.vm_steps_after,
        rep.gas_before,
        rep.gas_after,
        rep.translation_validated,
        json_str(&rep.stdout_before),
        json_str(&rep.stdout_after),
        rep.tests_passed,
        rep.tests_total,
        specs_json.join(","),
        views_json.join(","),
        rep.elapsed_ms,
        snap_json
    )
}

fn polyhedral_to_json(rep: &PolyhedralReport) -> String {
    let loops_json: Vec<String> = rep
        .loops
        .iter()
        .map(|l| {
            let acc_json: Vec<String> = l
                .accesses
                .iter()
                .map(|a| {
                    format!(
                        "{{\"array_or_var\":{},\"access_kind\":{},\"index_expr\":{},\"stride\":{},\"offset\":{}}}",
                        json_str(&a.array_or_var),
                        json_str(&a.access_kind),
                        json_str(&a.index_expr),
                        a.stride,
                        a.offset
                    )
                })
                .collect();
            let dep_json: Vec<String> = l
                .dependences
                .iter()
                .map(|d| {
                    let monoid = d
                        .reduction_monoid
                        .as_deref()
                        .map(json_str)
                        .unwrap_or_else(|| "null".to_string());
                    format!(
                        "{{\"variable\":{},\"kind\":{},\"distance\":{},\"is_reduction\":{},\"reduction_monoid\":{},\"blocks_simd\":{},\"note\":{}}}",
                        json_str(&d.variable),
                        json_str(&d.kind),
                        json_str(&d.distance),
                        d.is_reduction,
                        monoid,
                        d.blocks_simd,
                        json_str(&d.note)
                    )
                })
                .collect();
            let red_json: Vec<String> = l.reductions.iter().map(|r| json_str(r)).collect();
            let vec_json: Vec<String> = l
                .vectorized_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"loop_id\":{},\"fn_name\":{},\"loop_kind\":{},\"induction_var\":{},\"iteration_domain\":{},\"classification\":{},\"simd_vectorizable\":{},\"map_reduce_parallelizable\":{},\"estimated_simd4_speedup\":{:.2},\"work_t1_symbolic\":{},\"span_tinf_symbolic\":{},\"brent_parallelism_n64\":{:.2},\"accesses\":[{}],\"dependences\":[{}],\"reductions\":[{}],\"vectorized_by_spoke\":{{{}}}}}",
                l.loop_id,
                json_str(&l.fn_name),
                json_str(&l.loop_kind),
                json_str(&l.induction_var),
                json_str(&l.iteration_domain),
                json_str(&l.classification),
                l.simd_vectorizable,
                l.map_reduce_parallelizable,
                l.estimated_simd4_speedup,
                json_str(&l.work_t1_symbolic),
                json_str(&l.span_tinf_symbolic),
                l.brent_parallelism_n64,
                acc_json.join(","),
                dep_json.join(","),
                red_json.join(","),
                vec_json.join(",")
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_loops\":{},\"vectorizable_loops\":{},\"map_reduce_loops\":{},\"sequential_state_loops\":{},\"total_reductions\":{},\"max_simd4_speedup\":{:.2},\"elapsed_ms\":{},\"loops\":[{}]}}",
        rep.total_loops,
        rep.vectorizable_loops,
        rep.map_reduce_loops,
        rep.sequential_state_loops,
        rep.total_reductions,
        rep.max_simd4_speedup,
        rep.elapsed_ms,
        loops_json.join(",")
    )
}

fn wcet_to_json(rep: &TerminationWcetReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let wcep: Vec<String> = f.worst_case_path.iter().map(|s| json_str(s)).collect();
            let proofs: Vec<String> = f
                .loop_proofs
                .iter()
                .map(|lp| {
                    format!(
                        "{{\"stmt_id\":{},\"fn_name\":{},\"loop_header\":{},\"ranking_function\":{},\"bounded_below_vc\":{},\"strict_decrease_vc\":{},\"proven_terminating\":{},\"status\":{},\"witness_or_note\":{}}}",
                        lp.stmt_id,
                        json_str(&lp.fn_name),
                        json_str(&lp.loop_header),
                        json_str(&lp.ranking_function),
                        json_str(&lp.bounded_below_vc),
                        json_str(&lp.strict_decrease_vc),
                        lp.proven_terminating,
                        json_str(&lp.status),
                        json_str(&lp.witness_or_note)
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"proven_terminating\":{},\"bcet_symbolic\":{},\"wcet_symbolic\":{},\"bcet_cycles_n64\":{},\"wcet_cycles_n64\":{},\"jitter_ratio\":{:.2},\"worst_case_path\":[{}],\"loop_proofs\":[{}]}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.proven_terminating,
                json_str(&f.bcet_symbolic),
                json_str(&f.wcet_symbolic),
                f.bcet_cycles_n64,
                f.wcet_cycles_n64,
                f.jitter_ratio,
                wcep.join(","),
                proofs.join(",")
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"all_terminating\":{},\"total_functions\":{},\"total_loops_audited\":{},\"proven_terminating_loops\":{},\"diverging_or_unproven_loops\":{},\"module_wcet_cycles_n64\":{},\"module_bcet_cycles_n64\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.all_terminating,
        rep.total_functions,
        rep.total_loops_audited,
        rep.proven_terminating_loops,
        rep.diverging_or_unproven_loops,
        rep.module_wcet_cycles_n64,
        rep.module_bcet_cycles_n64,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn regalloc_to_json(rep: &RegAllocReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let ivs: Vec<String> = f
                .intervals
                .iter()
                .map(|iv| {
                    let col_json = iv
                        .assigned_color
                        .map(|c| c.to_string())
                        .unwrap_or_else(|| "null".to_string());
                    format!(
                        "{{\"var_name\":{},\"start_pc\":{},\"end_pc\":{},\"use_count\":{},\"max_loop_depth\":{},\"spill_weight\":{:.1},\"degree\":{},\"assigned_color\":{},\"aarch64_loc\":{},\"x86_64_loc\":{},\"linear_scan_loc\":{},\"spilled\":{}}}",
                        json_str(&iv.var_name),
                        iv.start_pc,
                        iv.end_pc,
                        iv.use_count,
                        iv.max_loop_depth,
                        iv.spill_weight,
                        iv.degree,
                        col_json,
                        json_str(&iv.aarch64_loc),
                        json_str(&iv.x86_64_loc),
                        json_str(&iv.linear_scan_loc),
                        iv.spilled
                    )
                })
                .collect();
            let eds: Vec<String> = f
                .edges
                .iter()
                .map(|e| {
                    format!(
                        "{{\"u\":{},\"v\":{},\"kind\":{}}}",
                        json_str(&e.u),
                        json_str(&e.v),
                        json_str(&e.kind)
                    )
                })
                .collect();
            let kempe: Vec<String> = f.kempe_order.iter().map(|s| json_str(s)).collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"k_registers\":{},\"virtual_regs\":{},\"interference_edges_count\":{},\"max_pressure_clique\":{},\"chromatic_colors_used\":{},\"coalesced_moves\":{},\"spilled_vars\":{},\"stack_frame_bytes\":{},\"intervals\":[{}],\"edges\":[{}],\"kempe_order\":[{}],\"mermaid_graph\":{},\"aarch64_asm\":{},\"x86_64_asm\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.k_registers,
                f.virtual_regs,
                f.interference_edges_count,
                f.max_pressure_clique,
                f.chromatic_colors_used,
                f.coalesced_moves,
                f.spilled_vars,
                f.stack_frame_bytes,
                ivs.join(","),
                eds.join(","),
                kempe.join(","),
                json_str(&f.mermaid_graph),
                json_str(&f.aarch64_asm),
                json_str(&f.x86_64_asm)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"k_registers\":{},\"total_functions\":{},\"total_virtual_regs\":{},\"total_interference_edges\":{},\"max_register_pressure\":{},\"total_coalesced_moves\":{},\"total_spills\":{},\"total_aarch64_insts\":{},\"total_x86_64_insts\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.k_registers,
        rep.total_functions,
        rep.total_virtual_regs,
        rep.total_interference_edges,
        rep.max_register_pressure,
        rep.total_coalesced_moves,
        rep.total_spills,
        rep.total_aarch64_insts,
        rep.total_x86_64_insts,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn escape_to_json(rep: &EscapeAnalysisReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let sites: Vec<String> = f
                .sites
                .iter()
                .map(|s| {
                    format!(
                        "{{\"site_id\":{},\"fn_name\":{},\"kind\":{},\"expr_summary\":{},\"escape_state\":{},\"promotion_strategy\":{},\"sroa_fields\":{},\"estimated_bytes_saved\":{},\"note\":{}}}",
                        s.site_id,
                        json_str(&s.fn_name),
                        json_str(&s.kind),
                        json_str(&s.expr_summary),
                        json_str(&s.escape_state),
                        json_str(&s.promotion_strategy),
                        s.sroa_fields,
                        s.estimated_bytes_saved,
                        json_str(&s.note)
                    )
                })
                .collect();
            let spk: Vec<String> = f
                .optimized_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"total_sites\":{},\"stack_or_sroa_sites\":{},\"rvo_sites\":{},\"heap_escape_sites\":{},\"bytes_saved_per_call\":{},\"sites\":[{}],\"optimized_by_spoke\":{{{}}}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.total_sites,
                f.stack_or_sroa_sites,
                f.rvo_sites,
                f.heap_escape_sites,
                f.bytes_saved_per_call,
                sites.join(","),
                spk.join(",")
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_alloc_sites\":{},\"stack_promoted_sites\":{},\"rvo_eliminated_sites\":{},\"sroa_scalarized_fields\":{},\"heap_escaping_sites\":{},\"total_bytes_saved_per_run\":{},\"heap_reduction_pct\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_alloc_sites,
        rep.stack_promoted_sites,
        rep.rvo_eliminated_sites,
        rep.sroa_scalarized_fields,
        rep.heap_escaping_sites,
        rep.total_bytes_saved_per_run,
        rep.heap_reduction_pct,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn microarch_to_json(rep: &MicroArchReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"uops_retired\":{},\"in_order_cycles\":{},\"ooo_cycles\":{},\"superscalar_ipc\":{:.2},\"alu_uops\":{},\"mul_div_uops\":{},\"mem_uops\":{},\"branch_uops\":{},\"branch_mispredicts\":{},\"l1d_hits\":{},\"l1d_misses\":{},\"bottleneck\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.uops_retired,
                f.in_order_cycles,
                f.ooo_cycles,
                f.superscalar_ipc,
                f.alu_uops,
                f.mul_div_uops,
                f.mem_uops,
                f.branch_uops,
                f.branch_mispredicts,
                f.l1d_hits,
                f.l1d_misses,
                json_str(&f.bottleneck)
            )
        })
        .collect();

    let brs_json: Vec<String> = rep
        .branch_sites
        .iter()
        .map(|b| {
            format!(
                "{{\"stmt_id\":{},\"fn_name\":{},\"branch_expr\":{},\"taken_count\":{},\"not_taken_count\":{},\"correct_predictions\":{},\"mispredictions\":{},\"accuracy_pct\":{:.1},\"penalty_cycles\":{}}}",
                b.stmt_id,
                json_str(&b.fn_name),
                json_str(&b.branch_expr),
                b.taken_count,
                b.not_taken_count,
                b.correct_predictions,
                b.mispredictions,
                b.accuracy_pct,
                b.penalty_cycles
            )
        })
        .collect();

    let ccs_json: Vec<String> = rep
        .cache_sites
        .iter()
        .map(|c| {
            format!(
                "{{\"site_label\":{},\"fn_name\":{},\"accesses\":{},\"l1_hits\":{},\"prefetch_hits\":{},\"misses\":{},\"hit_rate_pct\":{:.1},\"memory_cycles\":{}}}",
                json_str(&c.site_label),
                json_str(&c.fn_name),
                c.accesses,
                c.l1_hits,
                c.prefetch_hits,
                c.misses,
                c.hit_rate_pct,
                c.memory_cycles
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_uops_retired\":{},\"total_in_order_cycles\":{},\"total_ooo_cycles\":{},\"superscalar_ipc\":{:.2},\"ooo_speedup\":{:.2},\"total_branches\":{},\"branch_mispredictions\":{},\"branch_accuracy_pct\":{:.1},\"branch_penalty_cycles\":{},\"total_mem_accesses\":{},\"l1d_hits\":{},\"l1d_prefetch_hits\":{},\"l1d_misses\":{},\"l1d_hit_rate_pct\":{:.1},\"dominant_bottleneck\":{},\"elapsed_ms\":{},\"functions\":[{}],\"branch_sites\":[{}],\"cache_sites\":[{}]}}",
        rep.total_uops_retired,
        rep.total_in_order_cycles,
        rep.total_ooo_cycles,
        rep.superscalar_ipc,
        rep.ooo_speedup,
        rep.total_branches,
        rep.branch_mispredictions,
        rep.branch_accuracy_pct,
        rep.branch_penalty_cycles,
        rep.total_mem_accesses,
        rep.l1d_hits,
        rep.l1d_prefetch_hits,
        rep.l1d_misses,
        rep.l1d_hit_rate_pct,
        json_str(&rep.dominant_bottleneck),
        rep.elapsed_ms,
        fns_json.join(","),
        brs_json.join(","),
        ccs_json.join(",")
    )
}

fn schedule_to_json(rep: &InstructionScheduleReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let insts: Vec<String> = f
                .instructions
                .iter()
                .map(|i| {
                    format!(
                        "{{\"orig_idx\":{},\"sched_slot\":{},\"issue_cycle\":{},\"ready_cycle\":{},\"unit\":{},\"latency\":{},\"critical_height\":{},\"text\":{}}}",
                        i.orig_idx,
                        i.sched_slot,
                        i.issue_cycle,
                        i.ready_cycle,
                        json_str(&i.unit),
                        i.latency,
                        i.critical_height,
                        json_str(&i.text)
                    )
                })
                .collect();
            let edges: Vec<String> = f
                .dag_edges
                .iter()
                .map(|e| {
                    format!(
                        "{{\"from_idx\":{},\"to_idx\":{},\"kind\":{},\"latency\":{},\"var\":{}}}",
                        e.from_idx,
                        e.to_idx,
                        json_str(&e.kind),
                        e.latency,
                        json_str(&e.var)
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"inst_count\":{},\"dag_edges_count\":{},\"critical_path_cycles\":{},\"in_order_cycles_before\":{},\"scheduled_cycles_after\":{},\"stall_bubbles_before\":{},\"stall_bubbles_after\":{},\"bubbles_eliminated\":{},\"reordered_instructions\":{},\"speedup_ratio\":{:.2},\"instructions\":[{}],\"dag_edges\":[{}],\"unscheduled_listing\":{},\"scheduled_listing\":{},\"mermaid_dag\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.inst_count,
                f.dag_edges_count,
                f.critical_path_cycles,
                f.in_order_cycles_before,
                f.scheduled_cycles_after,
                f.stall_bubbles_before,
                f.stall_bubbles_after,
                f.bubbles_eliminated,
                f.reordered_instructions,
                f.speedup_ratio,
                insts.join(","),
                edges.join(","),
                json_str(&f.unscheduled_listing),
                json_str(&f.scheduled_listing),
                json_str(&f.mermaid_dag)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_instructions\":{},\"total_dag_edges\":{},\"total_cycles_before\":{},\"total_cycles_after\":{},\"total_bubbles_eliminated\":{},\"total_reordered_insts\":{},\"overall_speedup\":{:.2},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_instructions,
        rep.total_dag_edges,
        rep.total_cycles_before,
        rep.total_cycles_after,
        rep.total_bubbles_eliminated,
        rep.total_reordered_insts,
        rep.overall_speedup,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn autodiff_to_json(rep: &AutoDiffReport, snap: Option<&SyncSnapshot>) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let pts: Vec<String> = f
                .partials
                .iter()
                .map(|p| {
                    format!(
                        "{{\"param_name\":{},\"param_ty\":{},\"symbolic_derivative\":{},\"sample_point\":{},\"primal_value\":{},\"forward_dual_deriv\":{:.3},\"reverse_tape_adjoint\":{:.3},\"finite_diff_approx\":{:.3},\"dual_matches_reverse\":{}}}",
                        json_str(&p.param_name),
                        json_str(&p.param_ty),
                        json_str(&p.symbolic_derivative),
                        json_str(&p.sample_point),
                        p.primal_value,
                        p.forward_dual_deriv,
                        p.reverse_tape_adjoint,
                        p.finite_diff_approx,
                        p.dual_matches_reverse
                    )
                })
                .collect();
            let tp: Vec<String> = f
                .reverse_tape
                .iter()
                .map(|t| {
                    format!(
                        "{{\"tape_idx\":{},\"op_kind\":{},\"expr_label\":{},\"primal_val\":{:.2},\"adjoint_grad\":{:.3}}}",
                        t.tape_idx,
                        json_str(&t.op_kind),
                        json_str(&t.expr_label),
                        t.primal_val,
                        t.adjoint_grad
                    )
                })
                .collect();
            let gsp: Vec<String> = f
                .grad_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"differentiable_params\":{},\"tape_nodes_count\":{},\"lipschitz_bound\":{:.2},\"jacobian_norm_l1\":{:.2},\"all_partials_verified\":{},\"grad_fn_name\":{},\"partials\":[{}],\"reverse_tape\":[{}],\"grad_by_spoke\":{{{}}}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.differentiable_params,
                f.tape_nodes_count,
                f.lipschitz_bound,
                f.jacobian_norm_l1,
                f.all_partials_verified,
                json_str(&f.grad_fn_name),
                pts.join(","),
                tp.join(","),
                gsp.join(",")
            )
        })
        .collect();

    let snap_json = snap
        .map(snapshot_to_json)
        .unwrap_or_else(|| "null".to_string());

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"differentiable_functions\":{},\"total_partials\":{},\"verified_partials\":{},\"total_tape_nodes\":{},\"max_lipschitz_bound\":{:.2},\"all_gradients_verified\":{},\"synthesized_grad_fn_name\":{},\"elapsed_ms\":{},\"functions\":[{}],\"snapshot\":{}}}",
        rep.total_functions,
        rep.differentiable_functions,
        rep.total_partials,
        rep.verified_partials,
        rep.total_tape_nodes,
        rep.max_lipschitz_bound,
        rep.all_gradients_verified,
        json_str(&rep.synthesized_grad_fn_name),
        rep.elapsed_ms,
        fns_json.join(","),
        snap_json
    )
}

fn stability_to_json(rep: &NumericalStabilityReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let hzs: Vec<String> = f
                .hazards
                .iter()
                .map(|h| {
                    format!(
                        "{{\"site_id\":{},\"fn_name\":{},\"kind\":{},\"severity\":{},\"expr_summary\":{},\"max_error_ulps_or_bits\":{:.2},\"recommendation\":{}}}",
                        h.site_id,
                        json_str(&h.fn_name),
                        json_str(&h.kind),
                        json_str(&h.severity),
                        json_str(&h.expr_summary),
                        h.max_error_ulps_or_bits,
                        json_str(&h.recommendation)
                    )
                })
                .collect();
            let hsp: Vec<String> = f
                .hardened_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"condition_number_kappa\":{:.2},\"lipschitz_constant\":{:.2},\"overflow_risk_sites\":{},\"quantization_sites\":{},\"cancellation_sites\":{},\"stability_grade\":{},\"hazards\":[{}],\"hardened_by_spoke\":{{{}}}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.condition_number_kappa,
                f.lipschitz_constant,
                f.overflow_risk_sites,
                f.quantization_sites,
                f.cancellation_sites,
                json_str(&f.stability_grade),
                hzs.join(","),
                hsp.join(",")
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_hazards\":{},\"overflow_sites\":{},\"quantization_sites\":{},\"cancellation_sites\":{},\"max_condition_number\":{:.2},\"max_lipschitz_constant\":{:.2},\"well_conditioned_functions\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_hazards,
        rep.overflow_sites,
        rep.quantization_sites,
        rep.cancellation_sites,
        rep.max_condition_number,
        rep.max_lipschitz_constant,
        rep.well_conditioned_functions,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn actors_to_json(rep: &ActorConcurrencyReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let evs: Vec<String> = f
                .events
                .iter()
                .map(|e| {
                    let vc_s: Vec<String> = e.vector_clock.iter().map(|n| n.to_string()).collect();
                    format!(
                        "{{\"event_id\":{},\"actor_name\":{},\"op_kind\":{},\"variable\":{},\"vector_clock\":[{}],\"happens_before_note\":{}}}",
                        e.event_id,
                        json_str(&e.actor_name),
                        json_str(&e.op_kind),
                        json_str(&e.variable),
                        vc_s.join(","),
                        json_str(&e.happens_before_note)
                    )
                })
                .collect();
            let spk: Vec<String> = f
                .actor_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"actor_stages\":{},\"channel_capacity\":{},\"vector_clock_events\":{},\"concurrent_races_detected\":{},\"wait_for_cycles\":{},\"data_race_free\":{},\"deadlock_free\":{},\"topology_kind\":{},\"events\":[{}],\"actor_by_spoke\":{{{}}}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.actor_stages,
                f.channel_capacity,
                f.vector_clock_events,
                f.concurrent_races_detected,
                f.wait_for_cycles,
                f.data_race_free,
                f.deadlock_free,
                json_str(&f.topology_kind),
                evs.join(","),
                spk.join(",")
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_actor_stages\":{},\"total_vc_events\":{},\"total_races_detected\":{},\"total_wait_for_cycles\":{},\"all_data_race_free\":{},\"all_deadlock_free\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_actor_stages,
        rep.total_vc_events,
        rep.total_races_detected,
        rep.total_wait_for_cycles,
        rep.all_data_race_free,
        rep.all_deadlock_free,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn modelcheck_to_json(rep: &ModelCheckReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let svs: Vec<String> = f.state_variables.iter().map(|s| json_str(s)).collect();
            let props: Vec<String> = f
                .properties
                .iter()
                .map(|p| {
                    format!(
                        "{{\"property_id\":{},\"fn_name\":{},\"kind\":{},\"formula\":{},\"verified\":{},\"states_checked\":{},\"proof_or_counterexample\":{}}}",
                        p.property_id,
                        json_str(&p.fn_name),
                        json_str(&p.kind),
                        json_str(&p.formula),
                        p.verified,
                        p.states_checked,
                        json_str(&p.proof_or_counterexample)
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"reachable_states\":{},\"transitions_explored\":{},\"max_bfs_depth\":{},\"state_variables\":[{}],\"all_properties_verified\":{},\"properties\":[{}],\"tla_plus_spec\":{},\"mermaid_kripke\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.reachable_states,
                f.transitions_explored,
                f.max_bfs_depth,
                svs.join(","),
                f.all_properties_verified,
                props.join(","),
                json_str(&f.tla_plus_spec),
                json_str(&f.mermaid_kripke)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_reachable_states\":{},\"total_transitions\":{},\"total_properties\":{},\"verified_properties\":{},\"all_verified\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_reachable_states,
        rep.total_transitions,
        rep.total_properties,
        rep.verified_properties,
        rep.all_verified,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn zk_to_json(rep: &ZkCircuitReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let ws: Vec<String> = f
                .wires
                .iter()
                .map(|w| {
                    format!(
                        "{{\"wire_idx\":{},\"symbol\":{},\"visibility\":{},\"value_fp\":{}}}",
                        w.wire_idx,
                        json_str(&w.symbol),
                        json_str(&w.visibility),
                        w.value_fp
                    )
                })
                .collect();
            let cs: Vec<String> = f
                .constraints
                .iter()
                .map(|c| {
                    format!(
                        "{{\"constraint_id\":{},\"gate_kind\":{},\"a_linear_comb\":{},\"b_linear_comb\":{},\"c_linear_comb\":{},\"lhs_eval\":{},\"rhs_eval\":{},\"satisfied\":{},\"source_note\":{}}}",
                        c.constraint_id,
                        json_str(&c.gate_kind),
                        json_str(&c.a_linear_comb),
                        json_str(&c.b_linear_comb),
                        json_str(&c.c_linear_comb),
                        c.lhs_eval,
                        c.rhs_eval,
                        c.satisfied,
                        json_str(&c.source_note)
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"total_wires\":{},\"public_inputs\":{},\"private_witnesses\":{},\"r1cs_constraints\":{},\"satisfied_constraints\":{},\"all_constraints_satisfied\":{},\"multiplicative_depth\":{},\"wires\":[{}],\"constraints\":[{}],\"circom_template\":{},\"mermaid_circuit\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.total_wires,
                f.public_inputs,
                f.private_witnesses,
                f.r1cs_constraints,
                f.satisfied_constraints,
                f.all_constraints_satisfied,
                f.multiplicative_depth,
                ws.join(","),
                cs.join(","),
                json_str(&f.circom_template),
                json_str(&f.mermaid_circuit)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"field_modulus_str\":{},\"total_functions\":{},\"total_wires\":{},\"total_constraints\":{},\"satisfied_constraints\":{},\"all_circuits_satisfied\":{},\"max_multiplicative_depth\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        json_str(&rep.field_modulus_str),
        rep.total_functions,
        rep.total_wires,
        rep.total_constraints,
        rep.satisfied_constraints,
        rep.all_circuits_satisfied,
        rep.max_multiplicative_depth,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn sql_to_json(rep: &RelationalSqlReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let pns: Vec<String> = f
                .plan_nodes
                .iter()
                .map(|n| {
                    format!(
                        "{{\"step_id\":{},\"op_symbol\":{},\"expression\":{},\"est_rows_in\":{},\"est_rows_out\":{},\"vectorized_batch_cycles\":{}}}",
                        n.step_id,
                        json_str(&n.op_symbol),
                        json_str(&n.expression),
                        n.est_rows_in,
                        n.est_rows_out,
                        n.vectorized_batch_cycles
                    )
                })
                .collect();
            let spk: Vec<String> = f
                .query_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"relational_algebra_expr\":{},\"predicates_pushed_down\":{},\"columns_projected\":{},\"aggregations_count\":{},\"volcano_tuple_cycles\":{},\"vectorized_columnar_cycles\":{},\"columnar_speedup\":{:.2},\"plan_nodes\":[{}],\"ansi_sql_query\":{},\"query_by_spoke\":{{{}}}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                json_str(&f.relational_algebra_expr),
                f.predicates_pushed_down,
                f.columns_projected,
                f.aggregations_count,
                f.volcano_tuple_cycles,
                f.vectorized_columnar_cycles,
                f.columnar_speedup,
                pns.join(","),
                json_str(&f.ansi_sql_query),
                spk.join(",")
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"query_lifted_functions\":{},\"total_pushed_predicates\":{},\"total_aggregations\":{},\"total_volcano_cycles\":{},\"total_columnar_cycles\":{},\"overall_columnar_speedup\":{:.2},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.query_lifted_functions,
        rep.total_pushed_predicates,
        rep.total_aggregations,
        rep.total_volcano_cycles,
        rep.total_columnar_cycles,
        rep.overall_columnar_speedup,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn refinement_to_json(rep: &LiquidRefinementReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let bs: Vec<String> = f
                .bindings
                .iter()
                .map(|b| {
                    let qs: Vec<String> = b.qualifiers.iter().map(|q| json_str(q)).collect();
                    let lo_json = b
                        .lower_bound
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| "null".to_string());
                    let hi_json = b
                        .upper_bound
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| "null".to_string());
                    format!(
                        "{{\"symbol\":{},\"role\":{},\"base_type\":{},\"liquid_type\":{},\"lower_bound\":{},\"upper_bound\":{},\"qualifiers\":[{}]}}",
                        json_str(&b.symbol),
                        json_str(&b.role),
                        json_str(&b.base_type),
                        json_str(&b.liquid_type),
                        lo_json,
                        hi_json,
                        qs.join(",")
                    )
                })
                .collect();
            let hcs: Vec<String> = f
                .horn_clauses
                .iter()
                .map(|c| {
                    format!(
                        "{{\"clause_id\":{},\"kind\":{},\"premise_context\":{},\"lhs_refinement\":{},\"rhs_target\":{},\"horn_implication\":{},\"discharged\":{},\"solver_note\":{}}}",
                        c.clause_id,
                        json_str(&c.kind),
                        json_str(&c.premise_context),
                        json_str(&c.lhs_refinement),
                        json_str(&c.rhs_target),
                        json_str(&c.horn_implication),
                        c.discharged,
                        json_str(&c.solver_note)
                    )
                })
                .collect();
            let spk: Vec<String> = f
                .refined_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"refined_signature\":{},\"total_bindings\":{},\"total_qualifiers\":{},\"horn_clauses_total\":{},\"horn_clauses_discharged\":{},\"all_subtypes_valid\":{},\"fixpoint_iterations\":{},\"bindings\":[{}],\"horn_clauses\":[{}],\"smtlib2_horn_script\":{},\"refined_by_spoke\":{{{}}}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                json_str(&f.refined_signature),
                f.total_bindings,
                f.total_qualifiers,
                f.horn_clauses_total,
                f.horn_clauses_discharged,
                f.all_subtypes_valid,
                f.fixpoint_iterations,
                bs.join(","),
                hcs.join(","),
                json_str(&f.smtlib2_horn_script),
                spk.join(",")
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_refined_bindings\":{},\"total_qualifiers_inferred\":{},\"total_horn_clauses\":{},\"discharged_horn_clauses\":{},\"all_subtypes_verified\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_refined_bindings,
        rep.total_qualifiers_inferred,
        rep.total_horn_clauses,
        rep.discharged_horn_clauses,
        rep.all_subtypes_verified,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn prob_to_json(rep: &ProbabilisticEntropyReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let bps: Vec<String> = f
                .branch_posteriors
                .iter()
                .map(|b| {
                    format!(
                        "{{\"branch_id\":{},\"condition_expr\":{},\"taken_hits\":{},\"total_trials\":{},\"posterior_prob\":{:.2},\"surprise_bits\":{:.2}}}",
                        b.branch_id,
                        json_str(&b.condition_expr),
                        b.taken_hits,
                        b.total_trials,
                        b.posterior_prob,
                        b.surprise_bits
                    )
                })
                .collect();
            let hist: Vec<String> = f
                .posterior_histogram
                .iter()
                .map(|h| {
                    format!(
                        "{{\"bucket_label\":{},\"count\":{},\"probability\":{:.2},\"ascii_bar\":{}}}",
                        json_str(&h.bucket_label),
                        h.count,
                        h.probability,
                        json_str(&h.ascii_bar)
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"prior_distribution\":{},\"mcmc_particles\":{},\"acceptance_rate_pct\":{:.2},\"posterior_mean\":{:.2},\"posterior_variance\":{:.2},\"posterior_std_dev\":{:.2},\"credible_interval_90\":{},\"input_shannon_entropy_bits\":{:.2},\"output_shannon_entropy_bits\":{:.2},\"conditional_entropy_bits\":{:.2},\"mutual_information_bits\":{:.2},\"min_entropy_leakage_bits\":{:.2},\"qif_security_grade\":{},\"branch_posteriors\":[{}],\"posterior_histogram\":[{}],\"mermaid_factor_graph\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                json_str(&f.prior_distribution),
                f.mcmc_particles,
                f.acceptance_rate_pct,
                f.posterior_mean,
                f.posterior_variance,
                f.posterior_std_dev,
                json_str(&f.credible_interval_90),
                f.input_shannon_entropy_bits,
                f.output_shannon_entropy_bits,
                f.conditional_entropy_bits,
                f.mutual_information_bits,
                f.min_entropy_leakage_bits,
                json_str(&f.qif_security_grade),
                bps.join(","),
                hist.join(","),
                json_str(&f.mermaid_factor_graph)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_mcmc_samples\":{},\"max_mutual_info_bits\":{:.2},\"max_output_entropy_bits\":{:.2},\"total_branch_probes\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_mcmc_samples,
        rep.max_mutual_info_bits,
        rep.max_output_entropy_bits,
        rep.total_branch_probes,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn quantum_to_json(rep: &QuantumCircuitReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let regs: Vec<String> = f
                .registers
                .iter()
                .map(|r| {
                    format!(
                        "{{\"reg_id\":{},\"name\":{},\"role\":{},\"bit_width\":{},\"initial_state\":{},\"final_state\":{}}}",
                        r.reg_id,
                        json_str(&r.name),
                        json_str(&r.role),
                        r.bit_width,
                        json_str(&r.initial_state),
                        json_str(&r.final_state)
                    )
                })
                .collect();
            let gs: Vec<String> = f
                .gates
                .iter()
                .map(|g| {
                    format!(
                        "{{\"step_idx\":{},\"stage\":{},\"gate_op\":{},\"control_qubits\":{},\"target_qubits\":{},\"t_gate_cost\":{},\"source_note\":{}}}",
                        g.step_idx,
                        json_str(&g.stage),
                        json_str(&g.gate_op),
                        json_str(&g.control_qubits),
                        json_str(&g.target_qubits),
                        g.t_gate_cost,
                        json_str(&g.source_note)
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"logical_qubits\":{},\"ancilla_qubits\":{},\"total_qubits\":{},\"forward_gates\":{},\"uncompute_gates\":{},\"total_gates\":{},\"toffoli_count\":{},\"clifford_t_count\":{},\"circuit_depth\":{},\"ancilla_uncomputed_clean\":{},\"grover_search_space_bits\":{},\"grover_optimal_iterations\":{},\"grover_quadratic_speedup\":{:.2},\"registers\":[{}],\"gates\":[{}],\"openqasm3_source\":{},\"mermaid_circuit\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                f.logical_qubits,
                f.ancilla_qubits,
                f.total_qubits,
                f.forward_gates,
                f.uncompute_gates,
                f.total_gates,
                f.toffoli_count,
                f.clifford_t_count,
                f.circuit_depth,
                f.ancilla_uncomputed_clean,
                f.grover_search_space_bits,
                f.grover_optimal_iterations,
                f.grover_quadratic_speedup,
                regs.join(","),
                gs.join(","),
                json_str(&f.openqasm3_source),
                json_str(&f.mermaid_circuit)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_qubits_allocated\":{},\"total_reversible_gates\":{},\"total_toffoli_gates\":{},\"total_clifford_t_gates\":{},\"all_ancillas_uncomputed\":{},\"max_grover_speedup\":{:.2},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_qubits_allocated,
        rep.total_reversible_gates,
        rep.total_toffoli_gates,
        rep.total_clifford_t_gates,
        rep.all_ancillas_uncomputed,
        rep.max_grover_speedup,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn automata_to_json(rep: &MinimalDfaReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let alph: Vec<String> = f.alphabet.iter().map(|a| json_str(a)).collect();
            let sts: Vec<String> = f
                .states
                .iter()
                .map(|s| {
                    let tr: Vec<String> = s
                        .transitions
                        .iter()
                        .map(|(k, v)| format!("{}:{}", json_str(k), v))
                        .collect();
                    format!(
                        "{{\"state_id\":{},\"label\":{},\"access_word\":{},\"is_accepting\":{},\"output_class\":{},\"transitions\":{{{}}}}}",
                        s.state_id,
                        json_str(&s.label),
                        json_str(&s.access_word),
                        s.is_accepting,
                        json_str(&s.output_class),
                        tr.join(",")
                    )
                })
                .collect();
            let wits: Vec<String> = f
                .distinguishability_witnesses
                .iter()
                .map(|w| {
                    format!(
                        "{{\"state_a\":{},\"state_b\":{},\"distinguishing_suffix\":{},\"outcome_a\":{},\"outcome_b\":{}}}",
                        json_str(&w.state_a),
                        json_str(&w.state_b),
                        json_str(&w.distinguishing_suffix),
                        json_str(&w.outcome_a),
                        json_str(&w.outcome_b)
                    )
                })
                .collect();
            let spk: Vec<String> = f
                .fsm_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"alphabet\":[{}],\"unminimized_states\":{},\"minimal_states\":{},\"myhill_nerode_classes\":{},\"observation_table_queries\":{},\"synthesized_regex\":{},\"branchless_speedup\":{:.2},\"states\":[{}],\"distinguishability_witnesses\":[{}],\"fsm_by_spoke\":{{{}}},\"mermaid_dfa\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                alph.join(","),
                f.unminimized_states,
                f.minimal_states,
                f.myhill_nerode_classes,
                f.observation_table_queries,
                json_str(&f.synthesized_regex),
                f.branchless_speedup,
                sts.join(","),
                wits.join(","),
                spk.join(","),
                json_str(&f.mermaid_dfa)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_unminimized_states\":{},\"total_minimal_states\":{},\"total_lstar_queries\":{},\"all_myhill_nerode_minimal\":{},\"overall_branchless_speedup\":{:.2},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_unminimized_states,
        rep.total_minimal_states,
        rep.total_lstar_queries,
        rep.all_myhill_nerode_minimal,
        rep.overall_branchless_speedup,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn hls_to_json(rep: &HlsRtlReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let ops: Vec<String> = f
                .operations
                .iter()
                .map(|o| {
                    format!(
                        "{{\"op_id\":{},\"op_label\":{},\"functional_unit\":{},\"asap_cycle\":{},\"alap_cycle\":{},\"mobility\":{},\"scheduled_state\":{},\"fu_instance\":{},\"delay_ns\":{:.2},\"source_expr\":{}}}",
                        o.op_id,
                        json_str(&o.op_label),
                        json_str(&o.functional_unit),
                        o.asap_cycle,
                        o.alap_cycle,
                        o.mobility,
                        json_str(&o.scheduled_state),
                        json_str(&o.fu_instance),
                        o.delay_ns,
                        json_str(&o.source_expr)
                    )
                })
                .collect();
            let sts: Vec<String> = f
                .fsmd_states
                .iter()
                .map(|s| {
                    let aops: Vec<String> = s.active_ops.iter().map(|a| json_str(a)).collect();
                    let drtl: Vec<String> = s.datapath_rtl.iter().map(|d| json_str(d)).collect();
                    format!(
                        "{{\"state_id\":{},\"state_name\":{},\"active_ops\":[{}],\"datapath_rtl\":[{}],\"next_state_rule\":{},\"stage_delay_ns\":{:.2}}}",
                        s.state_id,
                        json_str(&s.state_name),
                        aops.join(","),
                        drtl.join(","),
                        json_str(&s.next_state_rule),
                        s.stage_delay_ns
                    )
                })
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"module_name\":{},\"total_cdfg_ops\":{},\"fsmd_states_count\":{},\"latency_cycles\":{},\"initiation_interval\":{},\"critical_path_ns\":{:.2},\"estimated_fmax_mhz\":{:.1},\"lut6_count\":{},\"flip_flops_count\":{},\"dsp48_blocks\":{},\"bram36_tiles\":{},\"operations\":[{}],\"fsmd_states\":[{}],\"systemverilog_rtl\":{},\"mermaid_fsmd\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                json_str(&f.module_name),
                f.total_cdfg_ops,
                f.fsmd_states_count,
                f.latency_cycles,
                f.initiation_interval,
                f.critical_path_ns,
                f.estimated_fmax_mhz,
                f.lut6_count,
                f.flip_flops_count,
                f.dsp48_blocks,
                f.bram36_tiles,
                ops.join(","),
                sts.join(","),
                json_str(&f.systemverilog_rtl),
                json_str(&f.mermaid_fsmd)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_cdfg_ops\":{},\"total_fsmd_states\":{},\"total_lut6\":{},\"total_flip_flops\":{},\"total_dsp48\":{},\"total_bram36\":{},\"min_fmax_mhz\":{:.1},\"all_pipelined_ii_1\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_cdfg_ops,
        rep.total_fsmd_states,
        rep.total_lut6,
        rep.total_flip_flops,
        rep.total_dsp48,
        rep.total_bram36,
        rep.min_fmax_mhz,
        rep.all_pipelined_ii_1,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn gpu_to_json(rep: &GpuSimtReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let divs: Vec<String> = f
                .divergence_sites
                .iter()
                .map(|d| {
                    format!(
                        "{{\"branch_id\":{},\"condition_expr\":{},\"active_lanes_taken\":{},\"active_lanes_not_taken\":{},\"active_mask_hex\":{},\"serialization_factor\":{},\"simd_efficiency_pct\":{:.2},\"mitigation_note\":{}}}",
                        d.branch_id,
                        json_str(&d.condition_expr),
                        d.active_lanes_taken,
                        d.active_lanes_not_taken,
                        json_str(&d.active_mask_hex),
                        d.serialization_factor,
                        d.simd_efficiency_pct,
                        json_str(&d.mitigation_note)
                    )
                })
                .collect();
            let banks: Vec<String> = f
                .bank_accesses
                .iter()
                .map(|b| {
                    format!(
                        "{{\"access_id\":{},\"buffer_expr\":{},\"stride_elements\":{},\"bank_conflict_ways\":{},\"conflict_free\":{},\"padding_recommendation\":{}}}",
                        b.access_id,
                        json_str(&b.buffer_expr),
                        b.stride_elements,
                        b.bank_conflict_ways,
                        b.conflict_free,
                        json_str(&b.padding_recommendation)
                    )
                })
                .collect();
            let spk: Vec<String> = f
                .host_dispatch_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"kernel_name\":{},\"warp_size\":{},\"workgroup_threads\":{},\"registers_per_thread\":{},\"shared_mem_bytes\":{},\"sm_occupancy_pct\":{:.1},\"warp_divergence_sites\":{},\"worst_serialization_factor\":{},\"warp_efficiency_pct\":{:.1},\"shared_mem_bank_conflicts\":{},\"arithmetic_intensity_flops_per_byte\":{:.2},\"roofline_bound\":{},\"estimated_gpu_speedup\":{:.1},\"divergence_sites\":[{}],\"bank_accesses\":[{}],\"cuda_ptx_source\":{},\"webgpu_wgsl_source\":{},\"metal_msl_source\":{},\"opencl_c_source\":{},\"host_dispatch_by_spoke\":{{{}}},\"mermaid_simt\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                json_str(&f.kernel_name),
                f.warp_size,
                f.workgroup_threads,
                f.registers_per_thread,
                f.shared_mem_bytes,
                f.sm_occupancy_pct,
                f.warp_divergence_sites,
                f.worst_serialization_factor,
                f.warp_efficiency_pct,
                f.shared_mem_bank_conflicts,
                f.arithmetic_intensity_flops_per_byte,
                json_str(&f.roofline_bound),
                f.estimated_gpu_speedup,
                divs.join(","),
                banks.join(","),
                json_str(&f.cuda_ptx_source),
                json_str(&f.webgpu_wgsl_source),
                json_str(&f.metal_msl_source),
                json_str(&f.opencl_c_source),
                spk.join(","),
                json_str(&f.mermaid_simt)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_gpu_kernels\":{},\"total_divergence_sites\":{},\"total_bank_conflicts\":{},\"avg_sm_occupancy_pct\":{:.1},\"avg_warp_efficiency_pct\":{:.1},\"max_gpu_speedup\":{:.1},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_gpu_kernels,
        rep.total_divergence_sites,
        rep.total_bank_conflicts,
        rep.avg_sm_occupancy_pct,
        rep.avg_warp_efficiency_pct,
        rep.max_gpu_speedup,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn fhe_to_json(rep: &FheCircuitReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let gs: Vec<String> = f
                .gates
                .iter()
                .map(|g| {
                    format!(
                        "{{\"gate_id\":{},\"gate_kind\":{},\"scheme_op\":{},\"rns_level\":{},\"ciphertext_degree\":{},\"noise_bits_after\":{:.1},\"remaining_budget_bits\":{:.1},\"source_expr\":{}}}",
                        g.gate_id,
                        json_str(&g.gate_kind),
                        json_str(&g.scheme_op),
                        g.rns_level,
                        g.ciphertext_degree,
                        g.noise_bits_after,
                        g.remaining_budget_bits,
                        json_str(&g.source_expr)
                    )
                })
                .collect();
            let spk: Vec<String> = f
                .fhe_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"fhe_scheme\":{},\"poly_modulus_degree_n\":{},\"coeff_modulus_bits_q\":{},\"plaintext_modulus_t\":{},\"security_bits_lambda\":{},\"multiplicative_depth\":{},\"relinearizations_count\":{},\"mod_switches_count\":{},\"oblivious_mux_gates\":{},\"bootstraps_inserted\":{},\"initial_noise_budget_bits\":{:.1},\"final_noise_budget_bits\":{:.1},\"decryption_verified\":{},\"sample_plaintext_out\":{},\"sample_decrypted_out\":{},\"gates\":[{}],\"openfhe_cpp_source\":{},\"fhe_by_spoke\":{{{}}},\"mermaid_fhe\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                json_str(&f.fhe_scheme),
                f.poly_modulus_degree_n,
                f.coeff_modulus_bits_q,
                f.plaintext_modulus_t,
                f.security_bits_lambda,
                f.multiplicative_depth,
                f.relinearizations_count,
                f.mod_switches_count,
                f.oblivious_mux_gates,
                f.bootstraps_inserted,
                f.initial_noise_budget_bits,
                f.final_noise_budget_bits,
                f.decryption_verified,
                f.sample_plaintext_out,
                f.sample_decrypted_out,
                gs.join(","),
                json_str(&f.openfhe_cpp_source),
                spk.join(","),
                json_str(&f.mermaid_fhe)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_fhe_gates\":{},\"total_relinearizations\":{},\"total_oblivious_muxes\":{},\"total_bootstraps\":{},\"max_multiplicative_depth\":{},\"min_remaining_noise_bits\":{:.1},\"all_decryptions_verified\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_fhe_gates,
        rep.total_relinearizations,
        rep.total_oblivious_muxes,
        rep.total_bootstraps,
        rep.max_multiplicative_depth,
        rep.min_remaining_noise_bits,
        rep.all_decryptions_verified,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn seplogic_to_json(rep: &SeparationLogicReport) -> String {
    let fns_json: Vec<String> = rep
        .functions
        .iter()
        .map(|f| {
            let cs: Vec<String> = f
                .cells
                .iter()
                .map(|c| {
                    format!(
                        "{{\"cell_id\":{},\"location_sym\":{},\"owner_var\":{},\"points_to_val\":{},\"permission_frac\":{},\"lifecycle_state\":{}}}",
                        c.cell_id,
                        json_str(&c.location_sym),
                        json_str(&c.owner_var),
                        json_str(&c.points_to_val),
                        json_str(&c.permission_frac),
                        json_str(&c.lifecycle_state)
                    )
                })
                .collect();
            let ps: Vec<String> = f
                .proof_steps
                .iter()
                .map(|p| {
                    format!(
                        "{{\"step_id\":{},\"stmt_summary\":{},\"pre_spatial_heap\":{},\"action_rule\":{},\"post_spatial_heap\":{},\"disjointness_verified\":{}}}",
                        p.step_id,
                        json_str(&p.stmt_summary),
                        json_str(&p.pre_spatial_heap),
                        json_str(&p.action_rule),
                        json_str(&p.post_spatial_heap),
                        p.disjointness_verified
                    )
                })
                .collect();
            let spk: Vec<String> = f
                .region_by_spoke
                .iter()
                .map(|(k, v)| format!("{}:{}", json_str(k), json_str(v)))
                .collect();
            format!(
                "{{\"fn_name\":{},\"signature\":{},\"spatial_precondition\":{},\"spatial_postcondition\":{},\"frame_invariant_r\":{},\"magic_wand_continuation\":{},\"heap_cells_tracked\":{},\"proof_steps_count\":{},\"no_use_after_free\":{},\"no_double_free\":{},\"no_memory_leak\":{},\"no_mutable_aliasing\":{},\"all_spatial_proofs_valid\":{},\"cells\":[{}],\"proof_steps\":[{}],\"region_by_spoke\":{{{}}},\"mermaid_seplogic\":{}}}",
                json_str(&f.fn_name),
                json_str(&f.signature),
                json_str(&f.spatial_precondition),
                json_str(&f.spatial_postcondition),
                json_str(&f.frame_invariant_r),
                json_str(&f.magic_wand_continuation),
                f.heap_cells_tracked,
                f.proof_steps_count,
                f.no_use_after_free,
                f.no_double_free,
                f.no_memory_leak,
                f.no_mutable_aliasing,
                f.all_spatial_proofs_valid,
                cs.join(","),
                ps.join(","),
                spk.join(","),
                json_str(&f.mermaid_seplogic)
            )
        })
        .collect();

    format!(
        "{{\"ok\":true,\"total_functions\":{},\"total_heap_cells\":{},\"total_proof_steps\":{},\"use_after_free_bugs\":{},\"double_free_bugs\":{},\"memory_leak_bugs\":{},\"aliasing_bugs\":{},\"all_memory_safe\":{},\"elapsed_ms\":{},\"functions\":[{}]}}",
        rep.total_functions,
        rep.total_heap_cells,
        rep.total_proof_steps,
        rep.use_after_free_bugs,
        rep.double_free_bugs,
        rep.memory_leak_bugs,
        rep.aliasing_bugs,
        rep.all_memory_safe,
        rep.elapsed_ms,
        fns_json.join(",")
    )
}

fn samples_to_json() -> String {
    let entries: Vec<String> = SAMPLES
        .iter()
        .map(|s| {
            format!(
                "{{\"id\":{},\"title\":{},\"description\":{}}}",
                json_str(s.id),
                json_str(s.title),
                json_str(s.description)
            )
        })
        .collect();
    format!("[{}]", entries.join(","))
}

fn send_response(
    stream: &mut TcpStream,
    status: u16,
    content_type: &str,
    body: &str,
) -> std::io::Result<()> {
    let reason = match status {
        200 => "OK",
        400 => "Bad Request",
        404 => "Not Found",
        _ => "Internal Server Error",
    };
    let header = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        status,
        reason,
        content_type,
        body.len()
    );
    stream.write_all(header.as_bytes())?;
    stream.write_all(body.as_bytes())?;
    stream.flush()
}

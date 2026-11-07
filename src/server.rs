use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;

use crate::complexity::ComplexityReport;
use crate::debugger::TimeTravelReport;
use crate::engine::{StarEngine, SyncSnapshot};
use crate::hub::Diagnostic;
use crate::json::{json_str, parse_flat_json_object};
use crate::lens::SpokeId;
use crate::merge::{MergeReport, SemanticDiffReport};
use crate::mutate::MutationReport;
use crate::quickcheck::QuickCheckReport;
use crate::repair::RepairReport;
use crate::runner::run_all_spokes;
use crate::samples::{find_sample, SAMPLES};
use crate::trace::TraceReport;
use crate::verify::{VerifyReport, VerifyStatus};
use crate::wasm::encode_base64;

const UI_HTML: &str = include_str!("ui.html");

pub fn serve_web_studio(port: u16) -> Result<(), String> {
    let addr = format!("127.0.0.1:{}", port);
    let listener = TcpListener::bind(&addr)
        .map_err(|e| format!("failed to bind http://{}: {}", addr, e))?;

    println!("StarLang v1.2 — 13-Spoke Bidirectional Compiler, WebAssembly, Time-Travel, Big-O, QuickCheck & Auto-Repair Studio running at:");
    println!("  -> http://{}", addr);
    println!("Edit Rust, Zig, C11, C++, Swift, Java, Go, Python, Ruby, LuaJIT, Perl 5, TypeScript, or Star S-Expr to sync all 13 spokes, compile native .wasm/.wat, time-travel debug, profile Big-O & gas, run QuickCheck shrinking, synthesize automated program repairs, 3-way AST merge, symbolic safety proofs & 14-engine verification.\n");

    serve_listener(listener)
}

pub fn serve_listener(listener: TcpListener) -> Result<(), String> {
    let default_sample = &SAMPLES[0];
    let engine = StarEngine::from_source(default_sample.initial_spoke, default_sample.source)
        .map_err(|d| d.to_string())?;
    let shared = Arc::new(Mutex::new(engine));

    for stream in listener.incoming() {
        if let Ok(stream) = stream {
            let shared_clone = Arc::clone(&shared);
            thread::spawn(move || {
                let _ = handle_client(stream, shared_clone);
            });
        }
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
    let path = parts[1].to_string();

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

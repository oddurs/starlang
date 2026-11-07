use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;

use crate::engine::{StarEngine, SyncSnapshot};
use crate::hub::Diagnostic;
use crate::json::{json_str, parse_flat_json_object};
use crate::lens::SpokeId;
use crate::mutate::MutationReport;
use crate::runner::run_all_spokes;
use crate::samples::{find_sample, SAMPLES};
use crate::trace::TraceReport;

const UI_HTML: &str = include_str!("ui.html");

pub fn serve_web_studio(port: u16) -> Result<(), String> {
    let addr = format!("127.0.0.1:{}", port);
    let listener = TcpListener::bind(&addr)
        .map_err(|e| format!("failed to bind http://{}: {}", addr, e))?;

    println!("StarLang v0.6 — 9-Spoke Bidirectional Compiler Studio running at:");
    println!("  -> http://{}", addr);
    println!("Edit Rust, C++, Swift, Java, Go, Python, Ruby, TypeScript, or Star S-Expr to sync all spokes, live VM, tests, coverage & mutation testing.\n");

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
        "{{\"revision\":{},\"active_spoke\":{},\"node_count\":{},\"can_undo\":{},\"can_redo\":{},\"coverage_pct\":{},\"covered_stmts\":{},\"total_stmts\":{},\"metadata_badges\":[{}],\"semantic_diagnostics\":[{}],\"symbols\":[{}],\"live_eval\":{},\"test_results\":[{}],\"views\":{{{}}}}}",
        snap.revision,
        json_str(snap.active_spoke.as_str()),
        snap.node_count,
        snap.can_undo,
        snap.can_redo,
        snap.coverage_pct,
        snap.covered_stmts,
        snap.total_stmts,
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

fn diagnostic_to_json(d: &Diagnostic) -> String {
    format!(
        "{{\"language\":{},\"message\":{},\"line\":{},\"col\":{}}}",
        json_str(&d.language),
        json_str(&d.message),
        d.line,
        d.col
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

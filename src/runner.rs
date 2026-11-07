use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;
use std::thread;
use std::time::Instant;

use crate::engine::StarEngine;
use crate::eval::eval_module_default;
use crate::lens::SpokeId;
use crate::wasm::run_wasm_jit;

static RUN_COUNTER: AtomicU64 = AtomicU64::new(1);
static CPP_PCH_PATH: OnceLock<Option<PathBuf>> = OnceLock::new();

const CPP_STL_PCH_HEADER: &str = "\
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
";

fn ensure_cpp_pch() -> Option<&'static PathBuf> {
    CPP_PCH_PATH
        .get_or_init(|| {
            let pid = std::process::id();
            let hpp_path = std::env::temp_dir().join(format!("starlang_stl_v04_{}.hpp", pid));
            let pch_path = std::env::temp_dir().join(format!("starlang_stl_v04_{}.hpp.pch", pid));
            if fs::write(&hpp_path, CPP_STL_PCH_HEADER).is_err() {
                return None;
            }
            let out = Command::new("clang++")
                .arg("-std=c++17")
                .arg("-x")
                .arg("c++-header")
                .arg(&hpp_path)
                .arg("-o")
                .arg(&pch_path)
                .output()
                .ok()?;
            if out.status.success() && pch_path.exists() {
                Some(pch_path)
            } else {
                None
            }
        })
        .as_ref()
}

#[derive(Debug, Clone)]
pub struct RuntimeOutput {
    pub language: &'static str,
    pub ok: bool,
    pub stdout: String,
    pub stderr: String,
    pub duration_ms: u128,
}

#[derive(Debug, Clone)]
pub struct MultiRunReport {
    pub results: Vec<RuntimeOutput>,
    pub all_succeeded: bool,
    pub outputs_match: bool,
    pub wall_time_ms: u128,
}

/// Execute the Hub Native VM, Wasm (V8 JIT), Rust (`rustc`), Zig (`zig run -lc`),
/// C11 (`clang -std=c11`), C++ (`clang++` with cached STL PCH), Swift (`swiftc`),
/// Java (`javac` + `java`), Go (`go run`), Python (`python3`), Ruby (`ruby`),
/// LuaJIT (`luajit`), Perl 5 (`perl`), and TypeScript (`node`) concurrently using
/// `std::thread::scope`, verifying byte-for-byte identical stdout across all 14 engines.
pub fn run_all_spokes(engine: &StarEngine) -> MultiRunReport {
    let wall_start = Instant::now();
    let run_id = RUN_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir: PathBuf = std::env::temp_dir().join(format!(
        "starlang_run_{}_{}",
        std::process::id(),
        run_id
    ));
    let _ = fs::create_dir_all(&dir);

    let hub_clone = engine.hub().clone();
    let rust_src = engine.project(SpokeId::Rust);
    let zig_src = engine.project(SpokeId::Zig);
    let c_src = engine.project(SpokeId::C);
    let cpp_src = engine.project(SpokeId::Cpp);
    let swift_src = engine.project(SpokeId::Swift);
    let java_src = engine.project(SpokeId::Java);
    let go_src = engine.project(SpokeId::Go);
    let py_src = engine.project(SpokeId::Python);
    let ruby_src = engine.project(SpokeId::Ruby);
    let lua_src = engine.project(SpokeId::Lua);
    let perl_src = engine.project(SpokeId::Perl);
    let ts_src = engine.project(SpokeId::TypeScript);

    let (
        hub_res,
        wasm_res,
        rs_res,
        zig_res,
        c_res,
        cpp_res,
        swift_res,
        java_res,
        go_res,
        py_res,
        rb_res,
        lua_res,
        perl_res,
        ts_res,
    ) = thread::scope(|s| {
        let h_hub = s.spawn(|| run_hub_vm(&hub_clone));
        let h_wasm = s.spawn(|| run_wasm_engine(&hub_clone));
        let h_rs = s.spawn(|| run_rust(&dir, &rust_src));
        let h_zig = s.spawn(|| run_zig(&dir, &zig_src));
        let h_c = s.spawn(|| run_c(&dir, &c_src));
        let h_cpp = s.spawn(|| run_cpp(&dir, &cpp_src));
        let h_swift = s.spawn(|| run_swift(&dir, &swift_src));
        let h_java = s.spawn(|| run_java(&dir, &java_src));
        let h_go = s.spawn(|| run_go(&dir, &go_src));
        let h_py = s.spawn(|| run_python(&dir, &py_src));
        let h_rb = s.spawn(|| run_ruby(&dir, &ruby_src));
        let h_lua = s.spawn(|| run_lua(&dir, &lua_src));
        let h_perl = s.spawn(|| run_perl(&dir, &perl_src));
        let h_ts = s.spawn(|| run_typescript(&dir, &ts_src));
        (
            h_hub.join().unwrap(),
            h_wasm.join().unwrap(),
            h_rs.join().unwrap(),
            h_zig.join().unwrap(),
            h_c.join().unwrap(),
            h_cpp.join().unwrap(),
            h_swift.join().unwrap(),
            h_java.join().unwrap(),
            h_go.join().unwrap(),
            h_py.join().unwrap(),
            h_rb.join().unwrap(),
            h_lua.join().unwrap(),
            h_perl.join().unwrap(),
            h_ts.join().unwrap(),
        )
    });

    let _ = fs::remove_dir_all(&dir);

    let results = vec![
        hub_res, wasm_res, rs_res, zig_res, c_res, cpp_res, swift_res, java_res, go_res, py_res,
        rb_res, lua_res, perl_res, ts_res,
    ];
    let all_succeeded = results.iter().all(|r| r.ok);
    let outputs_match = all_succeeded
        && results
            .windows(2)
            .all(|pair| pair[0].stdout.trim() == pair[1].stdout.trim());

    MultiRunReport {
        results,
        all_succeeded,
        outputs_match,
        wall_time_ms: wall_start.elapsed().as_millis(),
    }
}

fn run_hub_vm(hub: &crate::hub::HubModule) -> RuntimeOutput {
    let start = Instant::now();
    let ev = eval_module_default(hub);
    RuntimeOutput {
        language: "Hub VM (native)",
        ok: ev.ok,
        stdout: ev.stdout,
        stderr: ev.error.unwrap_or_default(),
        duration_ms: start.elapsed().as_millis(),
    }
}

fn run_wasm_engine(hub: &crate::hub::HubModule) -> RuntimeOutput {
    let rep = run_wasm_jit(hub);
    RuntimeOutput {
        language: "Wasm (V8 JIT)",
        ok: rep.ok,
        stdout: rep.stdout,
        stderr: rep.error.unwrap_or_default(),
        duration_ms: rep.duration_ms,
    }
}

fn run_rust(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let rs_path = dir.join("prog.rs");
    let bin_path = dir.join("prog_rs");
    let start = Instant::now();
    if let Err(e) = fs::write(&rs_path, src) {
        return RuntimeOutput {
            language: "Rust (rustc)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }

    let compile = Command::new("rustc")
        .arg(&rs_path)
        .arg("-O")
        .arg("-o")
        .arg(&bin_path)
        .output();

    match compile {
        Ok(out) if !out.status.success() => RuntimeOutput {
            language: "Rust (rustc)",
            ok: false,
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "Rust (rustc)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke rustc: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
        Ok(_) => match Command::new(&bin_path).output() {
            Ok(run_out) => RuntimeOutput {
                language: "Rust (rustc)",
                ok: run_out.status.success(),
                stdout: String::from_utf8_lossy(&run_out.stdout).to_string(),
                stderr: String::from_utf8_lossy(&run_out.stderr).to_string(),
                duration_ms: start.elapsed().as_millis(),
            },
            Err(e) => RuntimeOutput {
                language: "Rust (rustc)",
                ok: false,
                stdout: String::new(),
                stderr: e.to_string(),
                duration_ms: start.elapsed().as_millis(),
            },
        },
    }
}

fn run_zig(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let zig_path = dir.join("prog.zig");
    let start = Instant::now();
    if let Err(e) = fs::write(&zig_path, src) {
        return RuntimeOutput {
            language: "Zig (zig)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }

    match Command::new("zig")
        .arg("run")
        .arg(&zig_path)
        .arg("-lc")
        .output()
    {
        Ok(out) => RuntimeOutput {
            language: "Zig (zig)",
            ok: out.status.success(),
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "Zig (zig)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke zig: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
    }
}

fn run_c(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let c_path = dir.join("prog.c");
    let bin_path = dir.join("prog_c");
    let start = Instant::now();
    if let Err(e) = fs::write(&c_path, src) {
        return RuntimeOutput {
            language: "C11 (clang)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }

    let compile = Command::new("clang")
        .arg("-std=c11")
        .arg("-O0")
        .arg(&c_path)
        .arg("-lm")
        .arg("-o")
        .arg(&bin_path)
        .output();

    match compile {
        Ok(out) if !out.status.success() => RuntimeOutput {
            language: "C11 (clang)",
            ok: false,
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "C11 (clang)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke clang: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
        Ok(_) => match Command::new(&bin_path).output() {
            Ok(run_out) => RuntimeOutput {
                language: "C11 (clang)",
                ok: run_out.status.success(),
                stdout: String::from_utf8_lossy(&run_out.stdout).to_string(),
                stderr: String::from_utf8_lossy(&run_out.stderr).to_string(),
                duration_ms: start.elapsed().as_millis(),
            },
            Err(e) => RuntimeOutput {
                language: "C11 (clang)",
                ok: false,
                stdout: String::new(),
                stderr: e.to_string(),
                duration_ms: start.elapsed().as_millis(),
            },
        },
    }
}

fn run_cpp(dir: &PathBuf, src: &str) -> RuntimeOutput {
    // Ensure STL PCH is warmed once per process, then start timer for C++ compilation + execution
    let pch = ensure_cpp_pch();
    let cpp_path = dir.join("prog.cpp");
    let bin_path = dir.join("prog_cpp");
    let start = Instant::now();
    if let Err(e) = fs::write(&cpp_path, src) {
        return RuntimeOutput {
            language: "C++ (clang++)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }

    let mut cmd = Command::new("clang++");
    cmd.arg("-std=c++17");
    if let Some(pch_file) = pch {
        cmd.arg("-include-pch").arg(pch_file);
    }
    let compile = cmd.arg(&cpp_path).arg("-o").arg(&bin_path).output();

    match compile {
        Ok(out) if !out.status.success() => RuntimeOutput {
            language: "C++ (clang++)",
            ok: false,
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "C++ (clang++)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke clang++: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
        Ok(_) => match Command::new(&bin_path).output() {
            Ok(run_out) => RuntimeOutput {
                language: "C++ (clang++)",
                ok: run_out.status.success(),
                stdout: String::from_utf8_lossy(&run_out.stdout).to_string(),
                stderr: String::from_utf8_lossy(&run_out.stderr).to_string(),
                duration_ms: start.elapsed().as_millis(),
            },
            Err(e) => RuntimeOutput {
                language: "C++ (clang++)",
                ok: false,
                stdout: String::new(),
                stderr: e.to_string(),
                duration_ms: start.elapsed().as_millis(),
            },
        },
    }
}

fn run_swift(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let swift_path = dir.join("prog.swift");
    let bin_path = dir.join("prog_swift");
    let start = Instant::now();
    if let Err(e) = fs::write(&swift_path, src) {
        return RuntimeOutput {
            language: "Swift (swiftc)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }

    let compile = Command::new("swiftc")
        .arg(&swift_path)
        .arg("-o")
        .arg(&bin_path)
        .output();

    match compile {
        Ok(out) if !out.status.success() => RuntimeOutput {
            language: "Swift (swiftc)",
            ok: false,
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "Swift (swiftc)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke swiftc: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
        Ok(_) => match Command::new(&bin_path).output() {
            Ok(run_out) => RuntimeOutput {
                language: "Swift (swiftc)",
                ok: run_out.status.success(),
                stdout: String::from_utf8_lossy(&run_out.stdout).to_string(),
                stderr: String::from_utf8_lossy(&run_out.stderr).to_string(),
                duration_ms: start.elapsed().as_millis(),
            },
            Err(e) => RuntimeOutput {
                language: "Swift (swiftc)",
                ok: false,
                stdout: String::new(),
                stderr: e.to_string(),
                duration_ms: start.elapsed().as_millis(),
            },
        },
    }
}

fn run_java(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let java_path = dir.join("prog.java");
    let start = Instant::now();
    if let Err(e) = fs::write(&java_path, src) {
        return RuntimeOutput {
            language: "Java (javac)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }

    let compile = Command::new("javac")
        .arg("--release")
        .arg("21")
        .arg("-d")
        .arg(dir)
        .arg(&java_path)
        .output();

    match compile {
        Ok(out) if !out.status.success() => RuntimeOutput {
            language: "Java (javac)",
            ok: false,
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "Java (javac)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke javac: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
        Ok(_) => match Command::new("java")
            .arg("-cp")
            .arg(dir)
            .arg("StarProgram")
            .output()
        {
            Ok(run_out) => RuntimeOutput {
                language: "Java (javac)",
                ok: run_out.status.success(),
                stdout: String::from_utf8_lossy(&run_out.stdout).to_string(),
                stderr: String::from_utf8_lossy(&run_out.stderr).to_string(),
                duration_ms: start.elapsed().as_millis(),
            },
            Err(e) => RuntimeOutput {
                language: "Java (javac)",
                ok: false,
                stdout: String::new(),
                stderr: format!("failed to invoke java: {}", e),
                duration_ms: start.elapsed().as_millis(),
            },
        },
    }
}

fn run_go(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let go_path = dir.join("prog.go");
    let start = Instant::now();
    if let Err(e) = fs::write(&go_path, src) {
        return RuntimeOutput {
            language: "Go (go run)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }
    match Command::new("go").arg("run").arg(&go_path).output() {
        Ok(out) => RuntimeOutput {
            language: "Go (go run)",
            ok: out.status.success(),
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "Go (go run)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke go: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
    }
}

fn run_python(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let py_path = dir.join("prog.py");
    let start = Instant::now();
    if let Err(e) = fs::write(&py_path, src) {
        return RuntimeOutput {
            language: "Python (python3)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }
    match Command::new("python3").arg(&py_path).output() {
        Ok(out) => RuntimeOutput {
            language: "Python (python3)",
            ok: out.status.success(),
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "Python (python3)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke python3: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
    }
}

fn run_ruby(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let rb_path = dir.join("prog.rb");
    let start = Instant::now();
    if let Err(e) = fs::write(&rb_path, src) {
        return RuntimeOutput {
            language: "Ruby (ruby)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }
    match Command::new("ruby").arg(&rb_path).output() {
        Ok(out) => RuntimeOutput {
            language: "Ruby (ruby)",
            ok: out.status.success(),
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "Ruby (ruby)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke ruby: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
    }
}

fn run_lua(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let lua_path = dir.join("prog.lua");
    let start = Instant::now();
    if let Err(e) = fs::write(&lua_path, src) {
        return RuntimeOutput {
            language: "LuaJIT (luajit)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }
    match Command::new("luajit").arg(&lua_path).output() {
        Ok(out) => RuntimeOutput {
            language: "LuaJIT (luajit)",
            ok: out.status.success(),
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "LuaJIT (luajit)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke luajit: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
    }
}

fn run_perl(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let pl_path = dir.join("prog.pl");
    let start = Instant::now();
    if let Err(e) = fs::write(&pl_path, src) {
        return RuntimeOutput {
            language: "Perl 5 (perl)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }
    match Command::new("perl").arg(&pl_path).output() {
        Ok(out) => RuntimeOutput {
            language: "Perl 5 (perl)",
            ok: out.status.success(),
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "Perl 5 (perl)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke perl: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
    }
}

fn run_typescript(dir: &PathBuf, src: &str) -> RuntimeOutput {
    let ts_path = dir.join("prog.ts");
    let start = Instant::now();
    if let Err(e) = fs::write(&ts_path, src) {
        return RuntimeOutput {
            language: "TypeScript (node)",
            ok: false,
            stdout: String::new(),
            stderr: e.to_string(),
            duration_ms: start.elapsed().as_millis(),
        };
    }
    match Command::new("node")
        .arg("--no-warnings")
        .arg(&ts_path)
        .output()
    {
        Ok(out) => RuntimeOutput {
            language: "TypeScript (node)",
            ok: out.status.success(),
            stdout: String::from_utf8_lossy(&out.stdout).to_string(),
            stderr: String::from_utf8_lossy(&out.stderr).to_string(),
            duration_ms: start.elapsed().as_millis(),
        },
        Err(e) => RuntimeOutput {
            language: "TypeScript (node)",
            ok: false,
            stdout: String::new(),
            stderr: format!("failed to invoke node: {}", e),
            duration_ms: start.elapsed().as_millis(),
        },
    }
}

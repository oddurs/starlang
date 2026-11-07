# ★ StarLang

[![ci](https://github.com/oddurs/starlang/actions/workflows/ci.yml/badge.svg)](https://github.com/oddurs/starlang/actions/workflows/ci.yml)

A zero-dependency **star-topology bidirectional 12-language compiler & WebAssembly 1.0 backend** written in pure Rust (`std` only). Edit a program in **any** spoke language and the other 11 languages update immediately while preserving language-specific idioms via sidecar metadata on the central Hub AST — or compile the Hub AST directly to native `.wasm` bytecode + `.wat` disassembly.

```text
          Rust (.rs)          Go (.go)
               \                 /
     Zig (.zig) \               / Python (.py)
                 \             /
       C11 (.c) —— ★ Hub AST ★ —— Ruby (.rb)
                 /   /  |  \   \
     C++ (.cpp) /   /   |   \   \ LuaJIT (.lua)
               /   /    |    \   \
  Swift (.swift) Java  Wasm  TS   Star IR (.star)
```

## Highlights

- **12 Bidirectional Asymmetric Lenses (`get` / `put`)**: Hand-written lexers, recursive-descent parsers, and idiomatic pretty-printers for **Rust**, **Zig 0.16**, **Modern ISO C11**, **Modern C++17**, **Swift 6**, **Modern Java 21**, **Go**, **Python**, **Modern Ruby + RBS**, **LuaJIT + LuaCATS** (with exact 0-based ⇄ 1-based indexing and inclusive `for`-range bijections), **TypeScript**, and **Star S-Expr IR** (`GetPut` verified via property-based fuzzing).
- **Zero-Dependency WebAssembly 1.0 Binary (`.wasm`) & Text (`.wat`) Compiler**: Hand-encodes W3C WebAssembly 1.0 binary sections (`Type`, `Import`, `Function`, `Memory`, `Global`, `Export`, `Code`, `Data`) with bump-allocated 8-byte-slot structs/lists and structured loop control flow in pure `std` Rust, executing `main` and `test_*` exports in V8's `WebAssembly.instantiate` JIT and directly in the browser.
- **3-Way Cross-Language Semantic AST Merger & Diff**: Reconciles concurrent edits made in **two different languages** (e.g., Python + Zig or Lua + C++) directly on `NodeId`-aligned and LCS-aligned Hub AST nodes + sidecar metadata, projecting the unified result across all 12 languages or reporting pinpoint semantic conflicts.
- **Sidecar Metadata Preservation**: Editing Zig, C11, Python, Ruby, Lua, Java, or TypeScript preserves Rust borrow slices (`&[T]`, `&str`) and C++ pass-by-value/const-ref choices stored on Hub AST nodes.
- **Hub Symbolic Safety & Dead-Branch Verifier**: Runs Cousot interval abstract interpretation (`[lo, hi]`, disequalities, relational `idx < len(xs)`, loop widening `∇`) paired with concolic Hub VM counterexample probing to prove or refute division-by-zero, list out-of-bounds indexing, inline assertions, and `UNSAT` unreachable branches across all 12 languages.
- **Hub AST Mutation Testing & Auto-Test Hardening**: Mutates boundary conditions and operators directly on the Hub AST, runs polyglot unit tests in-memory against every mutant, and automatically synthesizes missing boundary assertions (`test_mutation_hardened`) across all 12 languages at once.
- **Sub-Millisecond Hub VM, Live Unit Tests & AST Coverage Tracer**: Executes `main()` and polyglot unit tests on every keystroke, reporting statement-level AST coverage %, function hotspots, call-graph traces, and uncovered dead branches.
- **Cross-Language Semantic Refactoring & Optimizer**: Scope- and type-directed symbol renaming plus constant folding and dead-branch pruning across all 12 spokes simultaneously.
- **13-Engine Parallel Differential Verification**: Compiles and runs native toolchains concurrently (`Hub VM`, `Wasm (V8 JIT)`, `rustc`, `zig run -lc`, `clang -std=c11`, `clang++` with cached STL PCH, `swiftc`, `javac`/`java`, `go run`, `python3`, `ruby`, `luajit`, `node`) and verifies byte-for-byte identical `stdout`.

## Quickstart

```bash
cargo run                         # Start 12-pane live Web Studio at http://127.0.0.1:7878
cargo run -- demo                 # End-to-end 12-spoke sync, Wasm JIT, 3-way merge, verify, mutate & fuzz demo
cargo run -- wasm                 # Compile Hub AST to W3C WebAssembly 1.0 (.wasm + .wat) & run in V8 JIT
cargo run -- merge                # 3-way concurrent cross-language Hub AST merge showcase
cargo run -- verify               # Prove Hub safety obligations & detect UNSAT dead branches
cargo run -- mutate --harden      # Run Hub AST mutation testing & synthesize boundary tests
cargo run -- trace                # Inspect Hub AST statement coverage %, hotspots & call trace
cargo run -- test path/to/prog.lua # Run polyglot unit tests in sub-ms via Hub VM
cargo run -- fuzz 100             # Property-based 12-spoke GetPut lens fuzzer (1,200 round-trips)
cargo test                        # Full integration + 13-engine differential test suite
```

## License

MIT

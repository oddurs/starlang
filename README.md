# ★ StarLang

[![ci](https://github.com/oddurs/starlang/actions/workflows/ci.yml/badge.svg)](https://github.com/oddurs/starlang/actions/workflows/ci.yml)

A zero-dependency **star-topology bidirectional 8-language compiler** written in pure Rust (`std` only). Edit a program in **any** spoke language and the other 7 languages update immediately while preserving language-specific idioms via sidecar metadata on the central Hub AST.

```text
          Rust (.rs)          Go (.go)
               \                 /
    C++ (.cpp) ——\             /—— Python (.py)
                  ★ Hub AST ★
  Swift (.swift) —/           \—— TypeScript (.ts)
               /                 \
         Java (.java)        Star IR (.star)
```

## Highlights

- **8 Bidirectional Asymmetric Lenses (`get` / `put`)**: Hand-written lexers, recursive-descent parsers, and idiomatic pretty-printers for **Rust**, **Modern C++17**, **Swift 6**, **Modern Java 21**, **Go**, **Python**, **TypeScript**, and **Star S-Expr IR** (`GetPut` verified via property-based fuzzing).
- **Sidecar Metadata Preservation**: Editing Python, Java, or TypeScript preserves Rust borrow slices (`&[T]`, `&str`) and C++ pass-by-value/const-ref choices stored on Hub AST nodes.
- **Sub-Millisecond Hub VM, Live Unit Tests & AST Coverage Tracer**: Executes `main()` and polyglot unit tests on every keystroke, reporting statement-level AST coverage %, function hotspots, call-graph traces, and uncovered dead branches.
- **Cross-Language Semantic Refactoring & Optimizer**: Scope- and type-directed symbol renaming plus constant folding and dead-branch pruning across all 8 spokes simultaneously.
- **8-Engine Parallel Differential Verification**: Compiles and runs native toolchains concurrently (`Hub VM`, `rustc`, `clang++` with cached STL PCH, `swiftc`, `javac`/`java`, `go run`, `python3`, `node`) and verifies byte-for-byte identical `stdout`.

## Quickstart

```bash
cargo run                         # Start 8-pane live Web Studio at http://127.0.0.1:7878
cargo run -- demo                 # End-to-end 8-spoke sync, refactor, diff & fuzz demo
cargo run -- trace                # Inspect Hub AST statement coverage %, hotspots & call trace
cargo run -- test path/to/prog.rs # Run polyglot unit tests in sub-ms via Hub VM
cargo run -- fuzz 100             # Property-based 8-spoke GetPut lens fuzzer (800 round-trips)
cargo test                        # Full integration + 8-engine differential test suite
```

## License

MIT

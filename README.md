# ★ StarLang

[![ci](https://github.com/oddurs/starlang/actions/workflows/ci.yml/badge.svg)](https://github.com/oddurs/starlang/actions/workflows/ci.yml)

A zero-dependency **star-topology bidirectional 9-language compiler** written in pure Rust (`std` only). Edit a program in **any** spoke language and the other 8 languages update immediately while preserving language-specific idioms via sidecar metadata on the central Hub AST.

```text
          Rust (.rs)          Go (.go)
               \                 /
    C++ (.cpp) ——\             /—— Python (.py)
                  \           /
  Swift (.swift) —— ★ Hub AST ★ —— Ruby (.rb)
                  /           \
    Java (.java) —/             \—— TypeScript (.ts)
               /                 \
                        Star IR (.star)
```

## Highlights

- **9 Bidirectional Asymmetric Lenses (`get` / `put`)**: Hand-written lexers, recursive-descent parsers, and idiomatic pretty-printers for **Rust**, **Modern C++17**, **Swift 6**, **Modern Java 21**, **Go**, **Python**, **Modern Ruby + RBS**, **TypeScript**, and **Star S-Expr IR** (`GetPut` verified via property-based fuzzing).
- **Sidecar Metadata Preservation**: Editing Python, Ruby, Java, or TypeScript preserves Rust borrow slices (`&[T]`, `&str`) and C++ pass-by-value/const-ref choices stored on Hub AST nodes.
- **Hub AST Mutation Testing & Auto-Test Hardening**: Mutates boundary conditions and operators directly on the Hub AST, runs polyglot unit tests in-memory against every mutant, and automatically synthesizes missing boundary assertions (`test_mutation_hardened`) across all 9 languages at once.
- **Sub-Millisecond Hub VM, Live Unit Tests & AST Coverage Tracer**: Executes `main()` and polyglot unit tests on every keystroke, reporting statement-level AST coverage %, function hotspots, call-graph traces, and uncovered dead branches.
- **Cross-Language Semantic Refactoring & Optimizer**: Scope- and type-directed symbol renaming plus constant folding and dead-branch pruning across all 9 spokes simultaneously.
- **9-Engine Parallel Differential Verification**: Compiles and runs native toolchains concurrently (`Hub VM`, `rustc`, `clang++` with cached STL PCH, `swiftc`, `javac`/`java`, `go run`, `python3`, `ruby`, `node`) and verifies byte-for-byte identical `stdout`.

## Quickstart

```bash
cargo run                         # Start 9-pane live Web Studio at http://127.0.0.1:7878
cargo run -- demo                 # End-to-end 9-spoke sync, mutation harden, diff & fuzz demo
cargo run -- mutate --harden      # Run Hub AST mutation testing & synthesize boundary tests
cargo run -- trace                # Inspect Hub AST statement coverage %, hotspots & call trace
cargo run -- test path/to/prog.rs # Run polyglot unit tests in sub-ms via Hub VM
cargo run -- fuzz 100             # Property-based 9-spoke GetPut lens fuzzer (900 round-trips)
cargo test                        # Full integration + 9-engine differential test suite
```

## License

MIT

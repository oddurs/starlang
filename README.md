# ★ StarLang

[![ci](https://github.com/oddurs/starlang/actions/workflows/ci.yml/badge.svg)](https://github.com/oddurs/starlang/actions/workflows/ci.yml)

A zero-dependency **star-topology bidirectional 10-language compiler** written in pure Rust (`std` only). Edit a program in **any** spoke language and the other 9 languages update immediately while preserving language-specific idioms via sidecar metadata on the central Hub AST.

```text
          Rust (.rs)          Go (.go)
               \                 /
      C11 (.c) —\               /— Python (.py)
                 \             /
    C++ (.cpp) ——— ★ Hub AST ★ ——— Ruby (.rb)
                 /             \
  Swift (.swift)/               \— TypeScript (.ts)
               /                 \
    Java (.java)          Star IR (.star)
```

## Highlights

- **10 Bidirectional Asymmetric Lenses (`get` / `put`)**: Hand-written lexers, recursive-descent parsers, and idiomatic pretty-printers for **Rust**, **Modern ISO C11**, **Modern C++17**, **Swift 6**, **Modern Java 21**, **Go**, **Python**, **Modern Ruby + RBS**, **TypeScript**, and **Star S-Expr IR** (`GetPut` verified via property-based fuzzing).
- **Sidecar Metadata Preservation**: Editing C11, Python, Ruby, Java, or TypeScript preserves Rust borrow slices (`&[T]`, `&str`) and C++ pass-by-value/const-ref choices stored on Hub AST nodes.
- **Hub Symbolic Safety & Dead-Branch Verifier**: Runs Cousot interval abstract interpretation (`[lo, hi]`, disequalities, relational `idx < len(xs)`, loop widening `∇`) paired with concolic Hub VM counterexample probing to prove or refute division-by-zero, list out-of-bounds indexing, inline assertions, and `UNSAT` unreachable branches across all 10 languages.
- **Hub AST Mutation Testing & Auto-Test Hardening**: Mutates boundary conditions and operators directly on the Hub AST, runs polyglot unit tests in-memory against every mutant, and automatically synthesizes missing boundary assertions (`test_mutation_hardened`) across all 10 languages at once.
- **Sub-Millisecond Hub VM, Live Unit Tests & AST Coverage Tracer**: Executes `main()` and polyglot unit tests on every keystroke, reporting statement-level AST coverage %, function hotspots, call-graph traces, and uncovered dead branches.
- **Cross-Language Semantic Refactoring & Optimizer**: Scope- and type-directed symbol renaming plus constant folding and dead-branch pruning across all 10 spokes simultaneously.
- **10-Engine Parallel Differential Verification**: Compiles and runs native toolchains concurrently (`Hub VM`, `rustc`, `clang -std=c11`, `clang++` with cached STL PCH, `swiftc`, `javac`/`java`, `go run`, `python3`, `ruby`, `node`) and verifies byte-for-byte identical `stdout`.

## Quickstart

```bash
cargo run                         # Start 10-pane live Web Studio at http://127.0.0.1:7878
cargo run -- demo                 # End-to-end 10-spoke sync, symbolic verify, mutation harden & fuzz demo
cargo run -- verify               # Prove Hub safety obligations & detect UNSAT dead branches
cargo run -- mutate --harden      # Run Hub AST mutation testing & synthesize boundary tests
cargo run -- trace                # Inspect Hub AST statement coverage %, hotspots & call trace
cargo run -- test path/to/prog.c  # Run polyglot unit tests in sub-ms via Hub VM
cargo run -- fuzz 100             # Property-based 10-spoke GetPut lens fuzzer (1,000 round-trips)
cargo test                        # Full integration + 10-engine differential test suite
```

## License

MIT

# ★ StarLang

A zero-dependency **star-topology bidirectional multi-language compiler** written in pure Rust (`std` only). Edit a program in **any** spoke language and every other language updates immediately while preserving language-specific idioms via sidecar metadata on the central Hub AST.

```text
          Rust (.rs)        Python (.py)
               \              /
    C++ (.cpp) —— ★ Central Hub AST ★ —— TypeScript (.ts)
               /      |       \
       Swift (.swift) Go (.go) Star IR (.star)
```

## Highlights

- **Bidirectional Asymmetric Lenses (`get` / `put`)**: Every spoke implements a hand-written lexer, recursive-descent parser, and idiomatic pretty-printer reconciled against the central Hub AST (`GetPut` verified via property-based fuzzing).
- **Sidecar Metadata Preservation**: Editing Python or TypeScript preserves Rust borrow slices (`&[T]`, `&str`) and C++ pass-by-value/const-ref choices stored on Hub AST nodes.
- **Sub-Millisecond Hub VM & Live Polyglot Unit Tests**: Executes `main()` and `#[test]` / `def test_*` / `func test_*` assertions on every keystroke.
- **Cross-Language Semantic Refactoring & Optimizer**: Scope- and type-directed symbol renaming plus constant folding and dead-branch pruning across all spokes at once.
- **Parallel Differential Verification**: Compiles and runs native toolchains concurrently (`Hub VM`, `rustc`, `clang++` with cached STL PCH, `swiftc`, `go run`, `python3`, `node`) and verifies byte-for-byte identical `stdout`.

## Quickstart

```bash
cargo run                         # Start live Web Studio at http://127.0.0.1:7878
cargo run -- demo                 # End-to-end multi-spoke sync, refactor, diff & fuzz demo
cargo run -- test path/to/prog.rs # Run polyglot unit tests in sub-ms via Hub VM
cargo run -- fuzz 100             # Property-based GetPut lens fuzzer across all spokes
cargo test                        # Full integration + differential runtime test suite
```

## License

MIT

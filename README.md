# ★ StarLang

[![ci](https://github.com/oddurs/starlang/actions/workflows/ci.yml/badge.svg)](https://github.com/oddurs/starlang/actions/workflows/ci.yml)

A zero-dependency **star-topology bidirectional 13-language compiler, WebAssembly 1.0 backend & polyglot time-travel debugger** written in pure Rust (`std` only). Edit a program in **any** spoke language and the other 12 languages update immediately while preserving language-specific idioms via sidecar metadata on the central Hub AST — or compile the Hub AST directly to native `.wasm` bytecode + `.wat` disassembly and scrub through time-travel execution steps across all 13 languages simultaneously.

```text
          Rust (.rs)          Go (.go)
               \                 /
     Zig (.zig) \               / Python (.py)
                 \             /
       C11 (.c) —— ★ Hub AST ★ —— Ruby (.rb)
                 /  /  |   \  \
     C++ (.cpp) /  /   |    \  \ LuaJIT (.lua)
               /  /    |     \  \
  Swift (.swift) Java Wasm Perl TS  Star IR (.star)
```

## Highlights

- **13 Bidirectional Asymmetric Lenses (`get` / `put`)**: Hand-written lexers, recursive-descent parsers, and idiomatic pretty-printers for **Rust**, **Zig 0.16**, **Modern ISO C11**, **Modern C++17**, **Swift 6**, **Modern Java 21**, **Go**, **Python**, **Modern Ruby + RBS**, **LuaJIT + LuaCATS** (0-based ⇄ 1-based indexing bijection), **Modern Perl 5.34** (`use feature 'signatures'`, arrayref/hashref dereferencing & type-directed string vs. numeric operators), **TypeScript**, and **Star S-Expr IR** (`GetPut` verified via property-based fuzzing).
- **Whitebox Concolic Path Explorer, Boundary-Negation Solver & Denning Lattice Information-Flow Taint Auditor (`concolic.rs`)**: Pairs concrete execution with symbolic path constraint recording ($\Pi = c_1 \wedge \dots \wedge c_k$), systematically solves negated branch boundaries (`a == b` $\leftrightarrow$ `a != b`, `a < b` $\leftrightarrow$ `a >= b`, list lengths & element predicates) to enumerate all feasible execution paths and synthesize path-covering unit tests (`test_concolic_<fn>`) across all 13 languages, while auditing explicit + implicit (`pc_taint`) Denning lattice flows (`Untrusted`, `Confidential`, `Sanitized`, `Clean`), dominating sanitizers, and constant-time side-channel branches.
- **Cytron Static Single Assignment (SSA), $\phi$-Node Placement, Liveness & Hoare-Logic Weakest-Precondition ($WP$) Contract Verifier (`ssa.rs`)**: Computes Immediate Dominators (`idom`), Cytron Dominance Frontiers (`DF`), minimal Iterated Dominance Frontier $\phi$-nodes (`tokens_2 = φ(BB0: tokens_0, BB6: tokens_1)`), backward iterative variable liveness (`live_in` / `live_out`), and Def-Use / Dead-Store chains, and synthesizes & proves Design-by-Contract (`requires`, `loop_invariant`, `ensures`) Hoare triples and Dijkstra Weakest-Precondition Verification Conditions across all 13 languages.
- **Programming-by-Example (PBE) Inductive Program Synthesizer & Dominator Control-Flow Graph (`synth.rs`)**: Synthesizes verified functions + unit tests directly from I/O examples (e.g., `clamp_bonus` or list-folding `sum_above`) via bottom-up enumerative search with **Observational Equivalence Pruning** across all 13 languages, and lowers Hub functions into Basic Blocks with iterative **Dominator Sets**, **Natural Loop Back-Edge** detection, and **Mermaid / Graphviz DOT** CFG export.
- **Counterexample-Guided Automated Program Repair (`repair.rs`) & Bisimulation Verifier**: Localizes failing unit tests or refuted symbolic safety obligations via time-travel backward slicing, searches candidate AST repairs across relational boundaries, accumulators, and safety divisor guards, validates patches against all 4 verification gates (Static Typecheck + Unit Tests + Symbolic Verifier + QuickCheck), and projects unified `- / +` patches across all 13 languages.
- **Asymptotic Big-O, Resource-Gas & 13-Spoke Code-Density Profiler**: Statically classifies loop-nesting and recursion complexity (`O(1)`, `O(N)`, `O(N²)`, `O(2^N)`), computes cyclomatic complexity and heap allocation sites, empirically curve-fits instruction gas across $N \in \{4, 8, 16, 32, 64\}$, and compares logic lines, tokens, and byte density across all 13 languages + `.wasm`.
- **Polyglot Property-Based QuickCheck, Invariant Synthesizer & Minimal Counterexample Shrinker**: Automatically property-tests every function across generated trials, verifies unoptimized-vs-optimized Hub equivalence, discovers algebraic postconditions (including conservation laws such as `result.accepted + result.rejected == len(costs)`), and Delta-Debug shrinks any failing input to a minimal counterexample rendered in all 13 languages.
- **Polyglot Time-Travel Debugger, 13-Spoke Line Mapper & Dynamic Backward Slicer**: Records deterministic step-by-step Hub VM traces, maps every AST statement to its exact 1-based line number across **all 13 languages simultaneously**, and computes dynamic data + control dependency backward causal slices for any variable or assertion.
- **Zero-Dependency WebAssembly 1.0 Binary (`.wasm`) & Text (`.wat`) Compiler**: Hand-encodes W3C WebAssembly 1.0 binary sections (`Type`, `Import`, `Function`, `Memory`, `Global`, `Export`, `Code`, `Data`) with bump-allocated 8-byte-slot structs/lists and structured loop control flow in pure `std` Rust, executing `main` and `test_*` exports in V8's `WebAssembly.instantiate` JIT and directly in the browser.
- **3-Way Cross-Language Semantic AST Merger & Diff**: Reconciles concurrent edits made in **two different languages** (e.g., Python + Zig or Perl + C++) directly on `NodeId`-aligned and LCS-aligned Hub AST nodes + sidecar metadata, projecting the unified result across all 13 languages or reporting pinpoint semantic conflicts.
- **Sidecar Metadata Preservation**: Editing Zig, C11, Python, Ruby, Lua, Perl, Java, or TypeScript preserves Rust borrow slices (`&[T]`, `&str`) and C++ pass-by-value/const-ref choices stored on Hub AST nodes.
- **Hub Symbolic Safety & Dead-Branch Verifier**: Runs Cousot interval abstract interpretation (`[lo, hi]`, disequalities, relational `idx < len(xs)`, loop widening `∇`) paired with concolic Hub VM counterexample probing to prove or refute division-by-zero, list out-of-bounds indexing, inline assertions, and `UNSAT` unreachable branches across all 13 languages.
- **Hub AST Mutation Testing & Auto-Test Hardening**: Mutates boundary conditions and operators directly on the Hub AST, runs polyglot unit tests in-memory against every mutant, and automatically synthesizes missing boundary assertions (`test_mutation_hardened`) across all 13 languages at once.
- **Sub-Millisecond Hub VM, Live Unit Tests & AST Coverage Tracer**: Executes `main()` and polyglot unit tests on every keystroke, reporting statement-level AST coverage %, function hotspots, call-graph traces, and uncovered dead branches.
- **Cross-Language Semantic Refactoring & Optimizer**: Scope- and type-directed symbol renaming plus constant folding and dead-branch pruning across all 13 spokes simultaneously.
- **14-Engine Parallel Differential Verification**: Compiles and runs native toolchains concurrently (`Hub VM`, `Wasm (V8 JIT)`, `rustc`, `zig run -lc`, `clang -std=c11`, `clang++` with cached STL PCH, `swiftc`, `javac`/`java`, `go run`, `python3`, `ruby`, `luajit`, `perl`, `node`) and verifies byte-for-byte identical `stdout`.

## Quickstart

```bash
cargo run                         # Start 13-pane live Web Studio at http://127.0.0.1:7878
cargo run -- demo                 # End-to-end 13-spoke sync, Wasm JIT, time-travel, Big-O, QuickCheck, merge & verify demo
cargo run -- concolic             # Whitebox concolic path explorer, boundary-negation solver & 13-spoke test synthesizer
cargo run -- security             # Audit Denning lattice taint flows, dominating sanitizers & constant-time side-channels
cargo run -- ssa                  # Compute Cytron SSA form, Dominance Frontiers, φ-nodes, Liveness & Def-Use chains
cargo run -- contracts            # Infer Hoare-Logic DbC contracts (requires/invariant/ensures) & prove WP VCs
cargo run -- synth                # Synthesize a verified polyglot function + unit test from I/O examples across 13 spokes
cargo run -- cfg                  # Analyze Basic-Block Control-Flow Graphs, Dominator sets, Natural Loops & Mermaid/DOT
cargo run -- complexity           # Profile static & empirical Big-O scaling (N=4..64), gas cost & 13-spoke density
cargo run -- quickcheck           # Run property-based QuickCheck, invariant discovery & counterexample shrinking
cargo run -- repair               # Localize faults via backward slicing & synthesize a 4-gate verified AST patch across 13 languages
cargo run -- debug                # Record 13-language time-travel trace & compute backward causal slice
cargo run -- wasm                 # Compile Hub AST to W3C WebAssembly 1.0 (.wasm + .wat) & run in V8 JIT
cargo run -- merge                # 3-way concurrent cross-language Hub AST merge showcase
cargo run -- verify               # Prove Hub safety obligations & detect UNSAT dead branches
cargo run -- mutate --harden      # Run Hub AST mutation testing & synthesize boundary tests
cargo run -- trace                # Inspect Hub AST statement coverage %, hotspots & call trace
cargo run -- test path/to/prog.pl # Run polyglot unit tests in sub-ms via Hub VM
cargo run -- fuzz 100             # Property-based 13-spoke GetPut lens fuzzer (1,300 round-trips)
cargo test                        # Full integration + 14-engine differential test suite
```

## License

MIT

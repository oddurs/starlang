use std::collections::BTreeMap;

use crate::complexity::{analyze_complexity, ComplexityReport};
use crate::concolic::{
    analyze_security_flow, explore_concolic_paths, ConcolicReport, SecurityFlowReport,
};
use crate::debugger::{record_time_travel_default, TimeTravelReport};
use crate::egraph::{
    partial_eval_module, superoptimize_egraph, EGraphReport, PartialEvalReport,
};
use crate::eval::{eval_module, eval_tests_default, EvalResult, TestResult};
use crate::hub::{Diagnostic, HubModule};
use crate::lens::SpokeId;
use crate::merge::{diff_modules, merge_concurrent_edits, MergeReport, SemanticDiffReport};
use crate::mutate::{harden_tests, mutate_module, HardenReport, MutationReport};
use crate::polyhedral::{
    analyze_polyhedral, prove_termination_and_wcet, PolyhedralReport, TerminationWcetReport,
};
use crate::quickcheck::{run_quickcheck, run_quickcheck_default, QuickCheckReport};
use crate::refactor::{list_symbols, optimize_module, rename_symbol, SymbolEntry};
use crate::regalloc::{
    allocate_registers_and_codegen, analyze_escape_and_lifetimes, EscapeAnalysisReport,
    RegAllocReport,
};
use crate::repair::{
    check_module_equivalence, inject_demo_bug, repair_module, EquivalenceReport, RepairReport,
};
use crate::spokes::lens_for;
use crate::ssa::{analyze_ssa, infer_hoare_contracts, HoareContractReport, ModuleSsaReport};
use crate::synth::{
    analyze_cfg, default_list_synth_spec, default_synth_spec, parse_synth_spec,
    synthesize_from_examples, ModuleCfgReport, SynthReport,
};
use crate::trace::{trace_module_default, TraceReport};
use crate::typecheck::{check_module, SemanticDiagnostic};
use crate::verify::{verify_module, VerifyReport};
use crate::wasm::{compile_wasm, run_wasm_jit, WasmArtifact, WasmRunReport};

const LIVE_PREVIEW_STEP_BUDGET: usize = 50_000;

#[derive(Debug, Clone)]
pub struct SyncSnapshot {
    pub revision: u64,
    pub active_spoke: SpokeId,
    pub node_count: usize,
    pub can_undo: bool,
    pub can_redo: bool,
    pub coverage_pct: u8,
    pub covered_stmts: usize,
    pub total_stmts: usize,
    pub safety_proven: usize,
    pub safety_total: usize,
    pub safety_refuted: usize,
    pub unreachable_count: usize,
    pub metadata_badges: Vec<String>,
    pub semantic_diagnostics: Vec<SemanticDiagnostic>,
    pub symbols: Vec<SymbolEntry>,
    pub live_eval: EvalResult,
    pub test_results: Vec<TestResult>,
    pub views: BTreeMap<&'static str, String>,
}

#[derive(Clone)]
struct HistoryEntry {
    hub: HubModule,
    spoke: SpokeId,
    revision: u64,
}

pub struct StarEngine {
    history: Vec<HistoryEntry>,
    cursor: usize,
    next_rev: u64,
}

impl StarEngine {
    pub fn new(hub: HubModule, initial_spoke: SpokeId) -> Self {
        let entry = HistoryEntry {
            hub,
            spoke: initial_spoke,
            revision: 1,
        };
        Self {
            history: vec![entry],
            cursor: 0,
            next_rev: 2,
        }
    }

    pub fn from_source(spoke: SpokeId, source: &str) -> Result<Self, Diagnostic> {
        let lens = lens_for(spoke);
        let empty = HubModule::new();
        let hub = lens.put(source, &empty)?;
        Ok(Self::new(hub, spoke))
    }

    fn current(&self) -> &HistoryEntry {
        &self.history[self.cursor]
    }

    pub fn hub(&self) -> &HubModule {
        &self.current().hub
    }

    pub fn revision(&self) -> u64 {
        self.current().revision
    }

    pub fn can_undo(&self) -> bool {
        self.cursor > 0
    }

    pub fn can_redo(&self) -> bool {
        self.cursor + 1 < self.history.len()
    }

    pub fn project(&self, spoke: SpokeId) -> String {
        lens_for(spoke).get(self.hub())
    }

    pub fn validate(&self) -> Vec<SemanticDiagnostic> {
        check_module(self.hub())
    }

    pub fn trace(&self) -> TraceReport {
        trace_module_default(self.hub())
    }

    pub fn mutate(&self) -> MutationReport {
        mutate_module(self.hub())
    }

    pub fn verify(&self) -> VerifyReport {
        verify_module(self.hub())
    }

    pub fn compile_wasm(&self) -> Result<WasmArtifact, String> {
        compile_wasm(self.hub())
    }

    pub fn run_wasm(&self) -> WasmRunReport {
        run_wasm_jit(self.hub())
    }

    pub fn time_travel(&self, slice_target: Option<&str>) -> TimeTravelReport {
        record_time_travel_default(self.hub(), slice_target)
    }

    pub fn complexity(&self) -> ComplexityReport {
        analyze_complexity(self.hub())
    }

    pub fn quickcheck(&self, trials_per_fn: Option<usize>) -> QuickCheckReport {
        match trials_per_fn {
            Some(n) => run_quickcheck(self.hub(), n, 0x57A4_2026_1100),
            None => run_quickcheck_default(self.hub()),
        }
    }

    /// Run Automated Program Repair (fault localization + 4-gate CEGIS patch synthesis).
    /// If `inject_if_healthy` is true and the module currently has 0 failing tests / refutations,
    /// injects a realistic fault first and then repairs it back to a verified state.
    pub fn repair(&mut self, inject_if_healthy: bool) -> (SyncSnapshot, RepairReport, Option<String>) {
        let mut injected_desc = None;
        let target_hub = {
            let initial_check = repair_module(self.hub());
            if initial_check.already_healthy && inject_if_healthy {
                let (buggy, desc) = inject_demo_bug(self.hub());
                injected_desc = Some(desc);
                buggy
            } else {
                self.hub().clone()
            }
        };

        let report = repair_module(&target_hub);
        if report.repaired && !report.already_healthy {
            let active = self.current().spoke;
            self.push_hub(report.repaired_hub.clone(), active);
        }
        (self.snapshot(), report, injected_desc)
    }

    /// Check α-equivalence and QuickCheck bisimulation equivalence between the current Hub and `source` in `spoke`.
    pub fn equiv_with(
        &self,
        spoke: SpokeId,
        source: &str,
        trials: usize,
    ) -> Result<EquivalenceReport, Diagnostic> {
        let other_hub = lens_for(spoke).put(source, self.hub())?;
        Ok(check_module_equivalence(self.hub(), &other_hub, trials))
    }

    /// Analyze Control-Flow Graphs (Basic Blocks, Dominator Trees, Natural Loops, Mermaid & DOT).
    pub fn cfg(&self) -> ModuleCfgReport {
        analyze_cfg(self.hub())
    }

    /// Compute Cytron Static Single Assignment (SSA) form, Dominance Frontiers, φ-nodes, Liveness & Def-Use chains.
    pub fn ssa(&self) -> ModuleSsaReport {
        analyze_ssa(self.hub())
    }

    /// Infer Design-by-Contract (DbC) Hoare Logic specifications (`requires`, `loop_invariant`, `ensures`)
    /// and verify Dijkstra Weakest-Precondition (`WP`) Verification Conditions across all 13 spokes.
    pub fn contracts(&self) -> HoareContractReport {
        infer_hoare_contracts(self.hub())
    }

    /// Run DART/KLEE-style Whitebox Concolic Path Exploration & Path-Coverage Unit Test Synthesis.
    /// If `inject_tests` is true, appends the synthesized path-covering `test_concolic_*` functions
    /// to the active Hub module and projects across all 13 spokes.
    pub fn concolic(&mut self, inject_tests: bool) -> (ConcolicReport, Option<SyncSnapshot>) {
        let rep = explore_concolic_paths(self.hub());
        let snap = if inject_tests && rep.synthesized_tests_count > 0 {
            let active = self.current().spoke;
            self.push_hub(rep.hub_with_tests.clone(), active);
            Some(self.snapshot())
        } else {
            None
        };
        (rep, snap)
    }

    /// Run Denning Lattice Information-Flow Taint Analysis, Sanitizer Verification & Constant-Time Side-Channel Auditing.
    pub fn security_flow(&self) -> SecurityFlowReport {
        analyze_security_flow(self.hub())
    }

    /// Run Equality Saturation & Congruence-Closure E-Graph Superoptimization.
    /// If `apply_to_hub` is true and rewrites or dead-branch eliminations were discovered,
    /// pushes the superoptimized Hub onto the history stack and returns the updated snapshot.
    pub fn egraph(&mut self, apply_to_hub: bool) -> (EGraphReport, Option<SyncSnapshot>) {
        let rep = superoptimize_egraph(self.hub());
        let snap = if apply_to_hub && (rep.expressions_optimized > 0 || rep.dead_branches_pruned > 0)
        {
            let active = self.current().spoke;
            self.push_hub(rep.optimized_hub.clone(), active);
            Some(self.snapshot())
        } else {
            None
        };
        (rep, snap)
    }

    /// Run Futamura-Projection Partial Evaluation, Interprocedural Constant/Enum Specialization,
    /// Bounded Loop Unrolling & E-Graph Superoptimization.
    pub fn partial_eval(
        &mut self,
        apply_to_hub: bool,
    ) -> (PartialEvalReport, Option<SyncSnapshot>) {
        let rep = partial_eval_module(self.hub());
        let snap = if apply_to_hub
            && (rep.specialized_calls > 0
                || rep.static_branches_folded > 0
                || rep.loops_unrolled > 0
                || rep.egraph_rewrites > 0)
        {
            let active = self.current().spoke;
            self.push_hub(rep.residual_hub.clone(), active);
            Some(self.snapshot())
        } else {
            None
        };
        (rep, snap)
    }

    /// Run Polyhedral Loop Dependence Analysis, Associative Monoid Reduction Recognition,
    /// Brent's Theorem Work-Span Parallelism & 13-Spoke SIMD / Map-Reduce Vectorization.
    pub fn polyhedral(&self) -> PolyhedralReport {
        analyze_polyhedral(self.hub())
    }

    /// Run Floyd-Turing Well-Founded Ranking Function Termination Verification &
    /// Implicit Path Enumeration (IPET) Symbolic BCET / WCET Timing Bound Analysis.
    pub fn termination_wcet(&self) -> TerminationWcetReport {
        prove_termination_and_wcet(self.hub())
    }

    /// Run Chaitin-Briggs Kempe-Stack Graph-Coloring & Poletto-Sarkar Linear-Scan Register Allocation
    /// and emit Dual-Target Native Assembly (AArch64 AAPCS64 & x86_64 System V AMD64).
    pub fn regalloc(&self, k_registers: Option<usize>) -> RegAllocReport {
        allocate_registers_and_codegen(self.hub(), k_registers)
    }

    /// Run Interprocedural Escape Analysis, Scalar Replacement of Aggregates (SROA),
    /// Return-Value Optimization (RVO) & 13-Spoke Stack/Arena Lifetime Synthesis.
    pub fn escape_analysis(&self) -> EscapeAnalysisReport {
        analyze_escape_and_lifetimes(self.hub())
    }

    /// Run Programming-by-Example (PBE) Observational-Equivalence Inductive Program Synthesis.
    /// If `inject_into_hub` is true and synthesis succeeds, appends the synthesized function
    /// and its unit test into the active Hub module and projects across all 13 spokes.
    pub fn synthesize(
        &mut self,
        spec_input: Option<&str>,
        inject_into_hub: bool,
    ) -> Result<(SynthReport, Option<SyncSnapshot>), String> {
        let spec = match spec_input.map(|s| s.trim()) {
            None | Some("") | Some("default") | Some("clamp_bonus") => default_synth_spec(),
            Some("sum_above") | Some("list") => default_list_synth_spec(),
            Some(raw) => parse_synth_spec(raw)?,
        };
        let report = synthesize_from_examples(&spec);
        let snap = if inject_into_hub && report.ok {
            let mut next_hub = self.hub().clone();
            if let Some(new_fn) = &report.synthesized_fn {
                next_hub.items.retain(|existing| match existing {
                    crate::hub::Item::Function(f) => f.name != new_fn.name,
                    _ => true,
                });
                next_hub
                    .items
                    .push(crate::hub::Item::Function(new_fn.clone()));
            }
            if let Some(new_test) = &report.synthesized_test {
                next_hub.items.retain(|existing| match existing {
                    crate::hub::Item::Test(t) => t.name != new_test.name,
                    _ => true,
                });
                next_hub
                    .items
                    .push(crate::hub::Item::Test(new_test.clone()));
            }
            let active = self.current().spoke;
            self.push_hub(next_hub, active);
            Some(self.snapshot())
        } else {
            None
        };
        Ok((report, snap))
    }

    /// Compute the pure semantic Hub AST delta between the current Hub and `source` in `spoke`.
    pub fn diff_with(&self, spoke: SpokeId, source: &str) -> Result<SemanticDiffReport, Diagnostic> {
        let next_hub = lens_for(spoke).put(source, self.hub())?;
        Ok(diff_modules(self.hub(), &next_hub))
    }

    /// Perform a 3-way concurrent semantic AST + sidecar metadata merge of edits made in
    /// `left_spoke` and `right_spoke` off the current Hub AST. If the merge is conflict-free
    /// and non-empty, commits the merged Hub AST to history and projects all 11 spokes.
    pub fn merge_concurrent(
        &mut self,
        left_spoke: SpokeId,
        left_src: &str,
        right_spoke: SpokeId,
        right_src: &str,
    ) -> Result<(SyncSnapshot, MergeReport), Diagnostic> {
        let report =
            merge_concurrent_edits(self.hub(), left_spoke, left_src, right_spoke, right_src)?;
        if report.clean && !report.applied_changes.is_empty() {
            self.push_hub(report.merged_hub.clone(), left_spoke);
        }
        Ok((self.snapshot(), report))
    }

    /// Auto-synthesize boundary unit test assertions to kill surviving Hub AST mutants across all 11 spokes.
    pub fn harden_tests(&mut self) -> (SyncSnapshot, HardenReport) {
        let (new_hub, report) = harden_tests(self.hub());
        let active = self.current().spoke;
        if report.added_assertions > 0 {
            self.push_hub(new_hub, active);
        }
        (self.snapshot(), report)
    }

    fn push_hub(&mut self, new_hub: HubModule, spoke: SpokeId) {
        if &new_hub == self.hub() {
            self.history[self.cursor].spoke = spoke;
            return;
        }
        self.history.truncate(self.cursor + 1);
        let rev = self.next_rev;
        self.next_rev += 1;
        self.history.push(HistoryEntry {
            hub: new_hub,
            spoke,
            revision: rev,
        });
        self.cursor = self.history.len() - 1;
    }

    /// Lift an edit from `spoke` into the central Hub, record history, and return projections.
    /// If syntax parsing fails, the Hub remains untouched and the syntax `Diagnostic` is returned.
    pub fn apply_edit(&mut self, spoke: SpokeId, source: &str) -> Result<SyncSnapshot, Diagnostic> {
        let lens = lens_for(spoke);
        let new_hub = lens.put(source, self.hub())?;
        self.push_hub(new_hub, spoke);
        Ok(self.snapshot())
    }

    /// Perform a scope-aware, type-directed symbol rename on the central Hub across all 6 spokes.
    pub fn rename_symbol(
        &mut self,
        target_spec: &str,
        new_name: &str,
    ) -> Result<(SyncSnapshot, usize), String> {
        let (new_hub, count) = rename_symbol(self.hub(), target_spec, new_name)?;
        let active = self.current().spoke;
        if count > 0 {
            self.push_hub(new_hub, active);
        }
        Ok((self.snapshot(), count))
    }

    /// Run constant folding, algebraic simplification, and dead-branch pruning on the central Hub.
    pub fn optimize(&mut self) -> (SyncSnapshot, usize) {
        let (new_hub, rewrites) = optimize_module(self.hub());
        let active = self.current().spoke;
        if rewrites > 0 {
            self.push_hub(new_hub, active);
        }
        (self.snapshot(), rewrites)
    }

    pub fn undo(&mut self) -> Option<SyncSnapshot> {
        if self.can_undo() {
            self.cursor -= 1;
            Some(self.snapshot())
        } else {
            None
        }
    }

    pub fn redo(&mut self) -> Option<SyncSnapshot> {
        if self.can_redo() {
            self.cursor += 1;
            Some(self.snapshot())
        } else {
            None
        }
    }

    pub fn snapshot(&self) -> SyncSnapshot {
        let hub = self.hub();
        let mut views = BTreeMap::new();
        for spoke in SpokeId::ALL {
            views.insert(spoke.as_str(), lens_for(spoke).get(hub));
        }
        let trace = trace_module_default(hub);
        let ver = verify_module(hub);
        SyncSnapshot {
            revision: self.revision(),
            active_spoke: self.current().spoke,
            node_count: hub.node_count(),
            can_undo: self.can_undo(),
            can_redo: self.can_redo(),
            coverage_pct: trace.coverage_pct,
            covered_stmts: trace.covered_stmts,
            total_stmts: trace.total_stmts,
            safety_proven: ver.proven_safe,
            safety_total: ver.total_obligations,
            safety_refuted: ver.refuted,
            unreachable_count: ver.unreachable_branches.len(),
            metadata_badges: hub.metadata_badges(),
            semantic_diagnostics: check_module(hub),
            symbols: list_symbols(hub),
            live_eval: eval_module(hub, LIVE_PREVIEW_STEP_BUDGET),
            test_results: eval_tests_default(hub),
            views,
        }
    }
}

use std::collections::BTreeMap;

use crate::eval::{eval_module, eval_tests_default, EvalResult, TestResult};
use crate::hub::{Diagnostic, HubModule};
use crate::lens::SpokeId;
use crate::merge::{diff_modules, merge_concurrent_edits, MergeReport, SemanticDiffReport};
use crate::mutate::{harden_tests, mutate_module, HardenReport, MutationReport};
use crate::refactor::{list_symbols, optimize_module, rename_symbol, SymbolEntry};
use crate::spokes::lens_for;
use crate::trace::{trace_module_default, TraceReport};
use crate::typecheck::{check_module, SemanticDiagnostic};
use crate::verify::{verify_module, VerifyReport};

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

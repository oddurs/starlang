use std::collections::{BTreeSet, HashSet};

use crate::hub::{
    AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl, HubModule, Intrinsic,
    Item, MatchArm, MatchPat, Metadata, NodeId, Param, Stmt, StructDecl, TestDecl, UnaryOp,
};
use crate::lens::SpokeId;
use crate::reconcile::reconcile_modules;
use crate::spokes::lens_for;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticDelta {
    pub kind: &'static str, // "added" | "removed" | "modified" | "metadata"
    pub scope: String,
    pub summary: String,
}

#[derive(Debug, Clone)]
pub struct SemanticDiffReport {
    pub identical: bool,
    pub deltas: Vec<SemanticDelta>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppliedChange {
    pub spoke: SpokeId,
    pub scope: String,
    pub summary: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MergeConflict {
    pub node_id: NodeId,
    pub scope: String,
    pub description: String,
    pub base_summary: String,
    pub left_spoke: SpokeId,
    pub left_summary: String,
    pub right_spoke: SpokeId,
    pub right_summary: String,
}

#[derive(Debug, Clone)]
pub struct MergeReport {
    pub clean: bool,
    pub merged_hub: HubModule,
    pub applied_changes: Vec<AppliedChange>,
    pub conflicts: Vec<MergeConflict>,
}

/// Lift two arbitrary source files (in potentially different languages) to the central Hub
/// and compute their pure semantic AST delta (ignoring language syntax & formatting differences).
pub fn diff_sources(
    left_spoke: SpokeId,
    left_src: &str,
    right_spoke: SpokeId,
    right_src: &str,
) -> Result<SemanticDiffReport, Diagnostic> {
    let empty = HubModule::new();
    let left_hub = lens_for(left_spoke).put(left_src, &empty)?;
    let right_hub = lens_for(right_spoke).put(right_src, &left_hub)?;
    Ok(diff_modules(&left_hub, &right_hub))
}

/// Compute a structured semantic diff between two `HubModule` ASTs.
pub fn diff_modules(old_hub: &HubModule, new_hub: &HubModule) -> SemanticDiffReport {
    let mut deltas = Vec::new();

    let mut matched_new = vec![false; new_hub.items.len()];

    for old_item in &old_hub.items {
        let old_key = item_key(old_item);
        let found_idx = new_hub
            .items
            .iter()
            .enumerate()
            .find(|(idx, ni)| !matched_new[*idx] && item_id_or_key_matches(old_item, ni))
            .map(|(idx, _)| idx);

        match found_idx {
            None => {
                deltas.push(SemanticDelta {
                    kind: "removed",
                    scope: old_key.clone(),
                    summary: format!("Removed {}", old_key),
                });
            }
            Some(idx) => {
                matched_new[idx] = true;
                diff_item_pair(old_item, &new_hub.items[idx], &mut deltas);
            }
        }
    }

    for (idx, new_item) in new_hub.items.iter().enumerate() {
        if !matched_new[idx] {
            let key = item_key(new_item);
            deltas.push(SemanticDelta {
                kind: "added",
                scope: key.clone(),
                summary: format!("Added {}", key),
            });
        }
    }

    SemanticDiffReport {
        identical: deltas.is_empty(),
        deltas,
    }
}

/// Lift concurrent edits made in `left_spoke` and `right_spoke` off a shared `base` Hub AST
/// and perform a 3-way structural AST + sidecar metadata merge.
pub fn merge_concurrent_edits(
    base: &HubModule,
    left_spoke: SpokeId,
    left_src: &str,
    right_spoke: SpokeId,
    right_src: &str,
) -> Result<MergeReport, Diagnostic> {
    let left_hub = lens_for(left_spoke).put(left_src, base)?;
    let right_hub = lens_for(right_spoke).put(right_src, base)?;
    Ok(merge_hub_modules(
        base,
        left_spoke,
        &left_hub,
        right_spoke,
        &right_hub,
    ))
}

/// Perform a 3-way structural AST merge of `left_hub` and `right_hub` relative to `base`.
pub fn merge_hub_modules(
    base: &HubModule,
    left_spoke: SpokeId,
    left_hub: &HubModule,
    right_spoke: SpokeId,
    right_hub: &HubModule,
) -> MergeReport {
    let mut changes = Vec::new();
    let mut conflicts = Vec::new();
    let mut merged_items = Vec::new();

    let base_ids: HashSet<NodeId> = base.items.iter().map(item_id).filter(|&id| id > 0).collect();

    let mut used_left = vec![false; left_hub.items.len()];
    let mut used_right = vec![false; right_hub.items.len()];

    let mut base_to_left: Vec<Option<usize>> = Vec::with_capacity(base.items.len());
    let mut base_to_right: Vec<Option<usize>> = Vec::with_capacity(base.items.len());

    for b_item in &base.items {
        let l_idx = find_matching_item(b_item, &left_hub.items, &used_left, &base_ids);
        if let Some(i) = l_idx {
            used_left[i] = true;
        }
        base_to_left.push(l_idx);

        let r_idx = find_matching_item(b_item, &right_hub.items, &used_right, &base_ids);
        if let Some(i) = r_idx {
            used_right[i] = true;
        }
        base_to_right.push(r_idx);
    }

    let mut left_cursor = 0usize;
    let mut right_cursor = 0usize;

    for (b_idx, b_item) in base.items.iter().enumerate() {
        if let Some(l_target) = base_to_left[b_idx] {
            while left_cursor < l_target {
                if !used_left[left_cursor] {
                    used_left[left_cursor] = true;
                    let added = &left_hub.items[left_cursor];
                    maybe_push_added_item(
                        added,
                        left_spoke,
                        right_spoke,
                        &right_hub.items,
                        &mut used_right,
                        &mut merged_items,
                        &mut changes,
                    );
                }
                left_cursor += 1;
            }
        }
        if let Some(r_target) = base_to_right[b_idx] {
            while right_cursor < r_target {
                if !used_right[right_cursor] {
                    used_right[right_cursor] = true;
                    let added = &right_hub.items[right_cursor];
                    let scope = item_key(added);
                    changes.push(AppliedChange {
                        spoke: right_spoke,
                        scope: scope.clone(),
                        summary: format!("Added {}", scope),
                    });
                    merged_items.push(added.clone());
                }
                right_cursor += 1;
            }
        }

        let scope = item_key(b_item);
        match (base_to_left[b_idx], base_to_right[b_idx]) {
            (Some(li), Some(ri)) => {
                left_cursor = left_cursor.max(li + 1);
                right_cursor = right_cursor.max(ri + 1);
                let merged = merge_item_3way(
                    b_item,
                    &left_hub.items[li],
                    &right_hub.items[ri],
                    left_spoke,
                    right_spoke,
                    &mut changes,
                    &mut conflicts,
                );
                merged_items.push(merged);
            }
            (None, Some(ri)) => {
                right_cursor = right_cursor.max(ri + 1);
                let r_item = &right_hub.items[ri];
                if sem_eq_item(b_item, r_item) {
                    changes.push(AppliedChange {
                        spoke: left_spoke,
                        scope: scope.clone(),
                        summary: format!("Deleted {}", scope),
                    });
                } else {
                    conflicts.push(MergeConflict {
                        node_id: item_id(b_item),
                        scope: scope.clone(),
                        description: format!(
                            "Delete/modify conflict on {}: deleted in {} while modified in {}",
                            scope,
                            left_spoke.display_name(),
                            right_spoke.display_name()
                        ),
                        base_summary: scope.clone(),
                        left_spoke,
                        left_summary: "(deleted)".to_string(),
                        right_spoke,
                        right_summary: item_key(r_item),
                    });
                    merged_items.push(r_item.clone());
                }
            }
            (Some(li), None) => {
                left_cursor = left_cursor.max(li + 1);
                let l_item = &left_hub.items[li];
                if sem_eq_item(b_item, l_item) {
                    changes.push(AppliedChange {
                        spoke: right_spoke,
                        scope: scope.clone(),
                        summary: format!("Deleted {}", scope),
                    });
                } else {
                    conflicts.push(MergeConflict {
                        node_id: item_id(b_item),
                        scope: scope.clone(),
                        description: format!(
                            "Modify/delete conflict on {}: modified in {} while deleted in {}",
                            scope,
                            left_spoke.display_name(),
                            right_spoke.display_name()
                        ),
                        base_summary: scope.clone(),
                        left_spoke,
                        left_summary: item_key(l_item),
                        right_spoke,
                        right_summary: "(deleted)".to_string(),
                    });
                    merged_items.push(l_item.clone());
                }
            }
            (None, None) => {
                changes.push(AppliedChange {
                    spoke: left_spoke,
                    scope: scope.clone(),
                    summary: format!("Deleted {} (convergent)", scope),
                });
            }
        }
    }

    // Flush trailing newly added items from Left and Right
    while left_cursor < left_hub.items.len() {
        if !used_left[left_cursor] {
            used_left[left_cursor] = true;
            let added = &left_hub.items[left_cursor];
            maybe_push_added_item(
                added,
                left_spoke,
                right_spoke,
                &right_hub.items,
                &mut used_right,
                &mut merged_items,
                &mut changes,
            );
        }
        left_cursor += 1;
    }
    while right_cursor < right_hub.items.len() {
        if !used_right[right_cursor] {
            used_right[right_cursor] = true;
            let added = &right_hub.items[right_cursor];
            let scope = item_key(added);
            changes.push(AppliedChange {
                spoke: right_spoke,
                scope: scope.clone(),
                summary: format!("Added {}", scope),
            });
            merged_items.push(added.clone());
        }
        right_cursor += 1;
    }

    let raw_merged = HubModule {
        items: merged_items,
        next_id: base.next_id.max(left_hub.next_id).max(right_hub.next_id),
    };
    let merged_hub = reconcile_modules(raw_merged, base, SpokeId::Star);

    MergeReport {
        clean: conflicts.is_empty(),
        merged_hub,
        applied_changes: changes,
        conflicts,
    }
}

fn maybe_push_added_item(
    added: &Item,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    right_items: &[Item],
    used_right: &mut [bool],
    merged_items: &mut Vec<Item>,
    changes: &mut Vec<AppliedChange>,
) {
    let key = item_key(added);
    // Check if Right added the exact same item convergently
    if let Some((ri, r_it)) = right_items
        .iter()
        .enumerate()
        .find(|(idx, ri)| !used_right[*idx] && item_key(ri) == key)
    {
        if sem_eq_item(added, r_it) {
            used_right[ri] = true;
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: key.clone(),
                summary: format!(
                    "Added {} (convergent in {} + {})",
                    key,
                    left_spoke.display_name(),
                    right_spoke.display_name()
                ),
            });
            merged_items.push(added.clone());
            return;
        }
    }
    changes.push(AppliedChange {
        spoke: left_spoke,
        scope: key.clone(),
        summary: format!("Added {}", key),
    });
    merged_items.push(added.clone());
}

fn find_matching_item(
    b_item: &Item,
    candidates: &[Item],
    used: &[bool],
    base_ids: &HashSet<NodeId>,
) -> Option<usize> {
    let bid = item_id(b_item);
    if bid > 0 && base_ids.contains(&bid) {
        if let Some((idx, _)) = candidates
            .iter()
            .enumerate()
            .find(|(idx, c)| !used[*idx] && same_item_kind(b_item, c) && item_id(c) == bid)
        {
            return Some(idx);
        }
    }
    let bkey = item_key(b_item);
    candidates
        .iter()
        .enumerate()
        .find(|(idx, c)| !used[*idx] && item_key(c) == bkey)
        .map(|(idx, _)| idx)
}

fn item_id_or_key_matches(a: &Item, b: &Item) -> bool {
    (same_item_kind(a, b) && item_id(a) > 0 && item_id(a) == item_id(b)) || item_key(a) == item_key(b)
}

fn same_item_kind(a: &Item, b: &Item) -> bool {
    matches!(
        (a, b),
        (Item::Struct(_), Item::Struct(_))
            | (Item::Enum(_), Item::Enum(_))
            | (Item::Function(_), Item::Function(_))
            | (Item::Test(_), Item::Test(_))
    )
}

fn item_id(item: &Item) -> NodeId {
    match item {
        Item::Struct(s) => s.id,
        Item::Enum(e) => e.id,
        Item::Function(f) => f.id,
        Item::Test(t) => t.id,
    }
}

fn item_key(item: &Item) -> String {
    match item {
        Item::Struct(s) => format!("struct {}", s.name),
        Item::Enum(e) => format!("enum {}", e.name),
        Item::Function(f) => format!("fn {}", f.name),
        Item::Test(t) => format!("test {}", t.name),
    }
}

#[allow(clippy::too_many_arguments)]
fn merge_item_3way(
    base: &Item,
    left: &Item,
    right: &Item,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> Item {
    match (base, left, right) {
        (Item::Enum(be), Item::Enum(le), Item::Enum(re)) => Item::Enum(merge_enum_3way(
            be,
            le,
            re,
            left_spoke,
            right_spoke,
            changes,
            conflicts,
        )),
        (Item::Struct(bs), Item::Struct(ls), Item::Struct(rs)) => Item::Struct(merge_struct_3way(
            bs,
            ls,
            rs,
            left_spoke,
            right_spoke,
            changes,
            conflicts,
        )),
        (Item::Function(bf), Item::Function(lf), Item::Function(rf)) => {
            Item::Function(merge_fn_3way(
                bf,
                lf,
                rf,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            ))
        }
        (Item::Test(bt), Item::Test(lt), Item::Test(rt)) => Item::Test(merge_test_3way(
            bt,
            lt,
            rt,
            left_spoke,
            right_spoke,
            changes,
            conflicts,
        )),
        _ => left.clone(),
    }
}

fn merge_scalar_3way<T: Clone + PartialEq>(
    base: &T,
    left: &T,
    right: &T,
    node_id: NodeId,
    scope: &str,
    field_desc: &str,
    fmt_val: impl Fn(&T) -> String,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> T {
    let l_changed = left != base;
    let r_changed = right != base;
    match (l_changed, r_changed) {
        (false, false) => base.clone(),
        (true, false) => {
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: scope.to_string(),
                summary: format!("Updated {}: {} -> {}", field_desc, fmt_val(base), fmt_val(left)),
            });
            left.clone()
        }
        (false, true) => {
            changes.push(AppliedChange {
                spoke: right_spoke,
                scope: scope.to_string(),
                summary: format!("Updated {}: {} -> {}", field_desc, fmt_val(base), fmt_val(right)),
            });
            right.clone()
        }
        (true, true) => {
            if left == right {
                changes.push(AppliedChange {
                    spoke: left_spoke,
                    scope: scope.to_string(),
                    summary: format!("Updated {} to {} (convergent)", field_desc, fmt_val(left)),
                });
                left.clone()
            } else {
                conflicts.push(MergeConflict {
                    node_id,
                    scope: scope.to_string(),
                    description: format!("Conflicting edits to {} in {}", field_desc, scope),
                    base_summary: fmt_val(base),
                    left_spoke,
                    left_summary: fmt_val(left),
                    right_spoke,
                    right_summary: fmt_val(right),
                });
                left.clone()
            }
        }
    }
}

fn merge_meta_3way(
    base: &Metadata,
    left: &Metadata,
    right: &Metadata,
    node_id: NodeId,
    scope: &str,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> Metadata {
    let mut keys: BTreeSet<&String> = BTreeSet::new();
    keys.extend(base.keys());
    keys.extend(left.keys());
    keys.extend(right.keys());

    let mut out = Metadata::new();
    for k in keys {
        let bv = base.get(k);
        let lv = left.get(k);
        let rv = right.get(k);
        let chosen = if lv == bv {
            if rv != bv {
                changes.push(AppliedChange {
                    spoke: right_spoke,
                    scope: scope.to_string(),
                    summary: format!(
                        "Metadata {} = {}",
                        k,
                        rv.map(|s| s.as_str()).unwrap_or("(removed)")
                    ),
                });
            }
            rv
        } else if rv == bv || lv == rv {
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: scope.to_string(),
                summary: format!(
                    "Metadata {} = {}",
                    k,
                    lv.map(|s| s.as_str()).unwrap_or("(removed)")
                ),
            });
            lv
        } else {
            conflicts.push(MergeConflict {
                node_id,
                scope: scope.to_string(),
                description: format!("Conflicting sidecar metadata '{}'", k),
                base_summary: bv.cloned().unwrap_or_else(|| "(unset)".to_string()),
                left_spoke,
                left_summary: lv.cloned().unwrap_or_else(|| "(unset)".to_string()),
                right_spoke,
                right_summary: rv.cloned().unwrap_or_else(|| "(unset)".to_string()),
            });
            lv
        };
        if let Some(v) = chosen {
            out.insert(k.clone(), v.clone());
        }
    }
    out
}

fn merge_enum_3way(
    base: &EnumDecl,
    left: &EnumDecl,
    right: &EnumDecl,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> EnumDecl {
    let scope = format!("enum {}", base.name);
    let name = merge_scalar_3way(
        &base.name,
        &left.name,
        &right.name,
        base.id,
        &scope,
        "enum name",
        |s| s.clone(),
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    let comments = merge_string_vec_3way(
        &base.comments,
        &left.comments,
        &right.comments,
        &scope,
        "doc comment",
        left_spoke,
        right_spoke,
        changes,
    );
    let variants = merge_string_vec_3way(
        &base.variants,
        &left.variants,
        &right.variants,
        &scope,
        "variant",
        left_spoke,
        right_spoke,
        changes,
    );
    let meta = merge_meta_3way(
        &base.meta,
        &left.meta,
        &right.meta,
        base.id,
        &scope,
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    EnumDecl {
        id: base.id,
        name,
        variants,
        comments,
        meta,
    }
}

#[allow(clippy::too_many_arguments)]
fn merge_string_vec_3way(
    base: &[String],
    left: &[String],
    right: &[String],
    scope: &str,
    label: &str,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
) -> Vec<String> {
    if left == base && right == base {
        return base.to_vec();
    }
    if left == base {
        for v in right {
            if !base.contains(v) {
                changes.push(AppliedChange {
                    spoke: right_spoke,
                    scope: scope.to_string(),
                    summary: format!("Added {} '{}'", label, v),
                });
            }
        }
        return right.to_vec();
    }
    if right == base || left == right {
        for v in left {
            if !base.contains(v) {
                changes.push(AppliedChange {
                    spoke: left_spoke,
                    scope: scope.to_string(),
                    summary: format!("Added {} '{}'", label, v),
                });
            }
        }
        return left.to_vec();
    }

    let mut out = Vec::new();
    for b in base {
        let in_l = left.contains(b);
        let in_r = right.contains(b);
        if in_l && in_r {
            out.push(b.clone());
        } else if !in_l {
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: scope.to_string(),
                summary: format!("Removed {} '{}'", label, b),
            });
        } else {
            changes.push(AppliedChange {
                spoke: right_spoke,
                scope: scope.to_string(),
                summary: format!("Removed {} '{}'", label, b),
            });
        }
    }
    for l in left {
        if !base.contains(l) && !out.contains(l) {
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: scope.to_string(),
                summary: format!("Added {} '{}'", label, l),
            });
            out.push(l.clone());
        }
    }
    for r in right {
        if !base.contains(r) && !out.contains(r) {
            changes.push(AppliedChange {
                spoke: right_spoke,
                scope: scope.to_string(),
                summary: format!("Added {} '{}'", label, r),
            });
            out.push(r.clone());
        }
    }
    out
}

fn merge_struct_3way(
    base: &StructDecl,
    left: &StructDecl,
    right: &StructDecl,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> StructDecl {
    let scope = format!("struct {}", base.name);
    let name = merge_scalar_3way(
        &base.name,
        &left.name,
        &right.name,
        base.id,
        &scope,
        "struct name",
        |s| s.clone(),
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    let comments = merge_string_vec_3way(
        &base.comments,
        &left.comments,
        &right.comments,
        &scope,
        "doc comment",
        left_spoke,
        right_spoke,
        changes,
    );
    let meta = merge_meta_3way(
        &base.meta,
        &left.meta,
        &right.meta,
        base.id,
        &scope,
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );

    let mut fields = Vec::new();
    let mut used_l = vec![false; left.fields.len()];
    let mut used_r = vec![false; right.fields.len()];

    for bf in &base.fields {
        let li = left
            .fields
            .iter()
            .enumerate()
            .find(|(idx, f)| !used_l[*idx] && ((bf.id > 0 && f.id == bf.id) || f.name == bf.name))
            .map(|(i, _)| i);
        let ri = right
            .fields
            .iter()
            .enumerate()
            .find(|(idx, f)| !used_r[*idx] && ((bf.id > 0 && f.id == bf.id) || f.name == bf.name))
            .map(|(i, _)| i);

        if let Some(i) = li {
            used_l[i] = true;
        }
        if let Some(i) = ri {
            used_r[i] = true;
        }

        match (li, ri) {
            (Some(l_idx), Some(r_idx)) => {
                let lf = &left.fields[l_idx];
                let rf = &right.fields[r_idx];
                let fscope = format!("{}.{}", scope, bf.name);
                let fname = merge_scalar_3way(
                    &bf.name,
                    &lf.name,
                    &rf.name,
                    bf.id,
                    &fscope,
                    "field name",
                    |s| s.clone(),
                    left_spoke,
                    right_spoke,
                    changes,
                    conflicts,
                );
                let fty = merge_scalar_3way(
                    &bf.ty,
                    &lf.ty,
                    &rf.ty,
                    bf.id,
                    &fscope,
                    "field type",
                    |t| t.display(),
                    left_spoke,
                    right_spoke,
                    changes,
                    conflicts,
                );
                let fmeta = merge_meta_3way(
                    &bf.meta,
                    &lf.meta,
                    &rf.meta,
                    bf.id,
                    &fscope,
                    left_spoke,
                    right_spoke,
                    changes,
                    conflicts,
                );
                fields.push(Field {
                    id: bf.id,
                    name: fname,
                    ty: fty,
                    meta: fmeta,
                });
            }
            (None, Some(r_idx)) => {
                let rf = &right.fields[r_idx];
                if rf.name == bf.name && rf.ty == bf.ty {
                    changes.push(AppliedChange {
                        spoke: left_spoke,
                        scope: scope.clone(),
                        summary: format!("Removed field '{}'", bf.name),
                    });
                } else {
                    conflicts.push(MergeConflict {
                        node_id: bf.id,
                        scope: format!("{}.{}", scope, bf.name),
                        description: format!("Field '{}' deleted vs modified", bf.name),
                        base_summary: format!("{}: {}", bf.name, bf.ty.display()),
                        left_spoke,
                        left_summary: "(deleted)".to_string(),
                        right_spoke,
                        right_summary: format!("{}: {}", rf.name, rf.ty.display()),
                    });
                    fields.push(rf.clone());
                }
            }
            (Some(l_idx), None) => {
                let lf = &left.fields[l_idx];
                if lf.name == bf.name && lf.ty == bf.ty {
                    changes.push(AppliedChange {
                        spoke: right_spoke,
                        scope: scope.clone(),
                        summary: format!("Removed field '{}'", bf.name),
                    });
                } else {
                    conflicts.push(MergeConflict {
                        node_id: bf.id,
                        scope: format!("{}.{}", scope, bf.name),
                        description: format!("Field '{}' modified vs deleted", bf.name),
                        base_summary: format!("{}: {}", bf.name, bf.ty.display()),
                        left_spoke,
                        left_summary: format!("{}: {}", lf.name, lf.ty.display()),
                        right_spoke,
                        right_summary: "(deleted)".to_string(),
                    });
                    fields.push(lf.clone());
                }
            }
            (None, None) => {}
        }
    }

    for (i, lf) in left.fields.iter().enumerate() {
        if !used_l[i] {
            if let Some((ri, rf)) = right
                .fields
                .iter()
                .enumerate()
                .find(|(idx, rf)| !used_r[*idx] && rf.name == lf.name)
            {
                used_r[ri] = true;
                if rf.ty != lf.ty {
                    conflicts.push(MergeConflict {
                        node_id: lf.id,
                        scope: format!("{}.{}", scope, lf.name),
                        description: format!("Added field '{}' with conflicting types", lf.name),
                        base_summary: "(none)".to_string(),
                        left_spoke,
                        left_summary: lf.ty.display(),
                        right_spoke,
                        right_summary: rf.ty.display(),
                    });
                }
            }
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: scope.clone(),
                summary: format!("Added field '{}: {}'", lf.name, lf.ty.display()),
            });
            fields.push(lf.clone());
        }
    }
    for (i, rf) in right.fields.iter().enumerate() {
        if !used_r[i] {
            changes.push(AppliedChange {
                spoke: right_spoke,
                scope: scope.clone(),
                summary: format!("Added field '{}: {}'", rf.name, rf.ty.display()),
            });
            fields.push(rf.clone());
        }
    }

    StructDecl {
        id: base.id,
        name,
        fields,
        comments,
        meta,
    }
}

fn merge_fn_3way(
    base: &FnDecl,
    left: &FnDecl,
    right: &FnDecl,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> FnDecl {
    let scope = format!("fn {}", base.name);
    let name = merge_scalar_3way(
        &base.name,
        &left.name,
        &right.name,
        base.id,
        &scope,
        "function name",
        |s| s.clone(),
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    let ret_ty = merge_scalar_3way(
        &base.ret_ty,
        &left.ret_ty,
        &right.ret_ty,
        base.id,
        &scope,
        "return type",
        |t| t.display(),
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    let comments = merge_string_vec_3way(
        &base.comments,
        &left.comments,
        &right.comments,
        &scope,
        "doc comment",
        left_spoke,
        right_spoke,
        changes,
    );
    let meta = merge_meta_3way(
        &base.meta,
        &left.meta,
        &right.meta,
        base.id,
        &scope,
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    let params = merge_params_3way(
        &base.params,
        &left.params,
        &right.params,
        base.id,
        &scope,
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    let body = merge_stmt_lists(
        &base.body,
        &left.body,
        &right.body,
        &scope,
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );

    FnDecl {
        id: base.id,
        name,
        params,
        ret_ty,
        body,
        comments,
        meta,
    }
}

#[allow(clippy::too_many_arguments)]
fn merge_params_3way(
    base: &[Param],
    left: &[Param],
    right: &[Param],
    fn_id: NodeId,
    scope: &str,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> Vec<Param> {
    if left.len() == base.len() && right.len() == base.len() {
        let mut out = Vec::with_capacity(base.len());
        for i in 0..base.len() {
            let bp = &base[i];
            let lp = &left[i];
            let rp = &right[i];
            let pscope = format!("{}::{}", scope, bp.name);
            let pname = merge_scalar_3way(
                &bp.name,
                &lp.name,
                &rp.name,
                bp.id,
                &pscope,
                "param name",
                |s| s.clone(),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let pty = merge_scalar_3way(
                &bp.ty,
                &lp.ty,
                &rp.ty,
                bp.id,
                &pscope,
                "param type",
                |t| t.display(),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let pmeta = merge_meta_3way(
                &bp.meta,
                &lp.meta,
                &rp.meta,
                bp.id,
                &pscope,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            out.push(Param {
                id: bp.id,
                name: pname,
                ty: pty,
                meta: pmeta,
            });
        }
        return out;
    }

    let l_sig_same = sem_eq_params(base, left);
    let r_sig_same = sem_eq_params(base, right);
    if l_sig_same && !r_sig_same {
        changes.push(AppliedChange {
            spoke: right_spoke,
            scope: scope.to_string(),
            summary: format!("Updated parameter list ({})", fmt_params(right)),
        });
        return right.to_vec();
    }
    if !l_sig_same && (r_sig_same || sem_eq_params(left, right)) {
        changes.push(AppliedChange {
            spoke: left_spoke,
            scope: scope.to_string(),
            summary: format!("Updated parameter list ({})", fmt_params(left)),
        });
        return left.to_vec();
    }

    conflicts.push(MergeConflict {
        node_id: fn_id,
        scope: scope.to_string(),
        description: format!("Conflicting parameter list edits on {}", scope),
        base_summary: fmt_params(base),
        left_spoke,
        left_summary: fmt_params(left),
        right_spoke,
        right_summary: fmt_params(right),
    });
    left.to_vec()
}

fn merge_test_3way(
    base: &TestDecl,
    left: &TestDecl,
    right: &TestDecl,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> TestDecl {
    let scope = format!("test {}", base.name);
    let name = merge_scalar_3way(
        &base.name,
        &left.name,
        &right.name,
        base.id,
        &scope,
        "test name",
        |s| s.clone(),
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    let comments = merge_string_vec_3way(
        &base.comments,
        &left.comments,
        &right.comments,
        &scope,
        "doc comment",
        left_spoke,
        right_spoke,
        changes,
    );
    let meta = merge_meta_3way(
        &base.meta,
        &left.meta,
        &right.meta,
        base.id,
        &scope,
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    let body = merge_stmt_lists(
        &base.body,
        &left.body,
        &right.body,
        &scope,
        left_spoke,
        right_spoke,
        changes,
        conflicts,
    );
    TestDecl {
        id: base.id,
        name,
        body,
        comments,
        meta,
    }
}

/// Align `side` statements to `base` statements monotonically using:
/// 1) exact `NodeId` match (from `reconcile_modules`), and
/// 2) structural LCS fallback for any remaining unmatched statements.
fn align_stmts_to_base(base: &[Stmt], side: &[Stmt]) -> Vec<Option<usize>> {
    let b_len = base.len();
    let s_len = side.len();
    if b_len == 0 || s_len == 0 {
        return vec![None; b_len];
    }

    // Build LCS dynamic programming table where matching either `NodeId` (with compatible kind)
    // or full semantic statement equality scores a match (exact `sem_eq_stmt` weighted higher!).
    let mut dp = vec![vec![0usize; s_len + 1]; b_len + 1];
    for bi in (0..b_len).rev() {
        for si in (0..s_len).rev() {
            let weight = stmt_match_weight(&base[bi], &side[si]);
            let skip = dp[bi + 1][si].max(dp[bi][si + 1]);
            if weight > 0 {
                dp[bi][si] = skip.max(weight + dp[bi + 1][si + 1]);
            } else {
                dp[bi][si] = skip;
            }
        }
    }

    let mut mapping = vec![None; b_len];
    let mut bi = 0;
    let mut si = 0;
    while bi < b_len && si < s_len {
        let weight = stmt_match_weight(&base[bi], &side[si]);
        if weight > 0 && dp[bi][si] == weight + dp[bi + 1][si + 1] {
            mapping[bi] = Some(si);
            bi += 1;
            si += 1;
        } else if dp[bi + 1][si] >= dp[bi][si + 1] {
            bi += 1;
        } else {
            si += 1;
        }
    }
    mapping
}

fn stmt_match_weight(b: &Stmt, s: &Stmt) -> usize {
    if sem_eq_stmt(b, s) {
        return 4;
    }
    let bid = stmt_id(b);
    let sid = stmt_id(s);
    if bid > 0 && bid == sid && same_stmt_family(b, s) {
        return 3;
    }
    if same_stmt_anchor(b, s) {
        return 2;
    }
    0
}

fn same_stmt_family(a: &Stmt, b: &Stmt) -> bool {
    matches!(
        (a, b),
        (Stmt::Comment { .. }, Stmt::Comment { .. })
            | (Stmt::Let { .. }, Stmt::Let { .. })
            | (Stmt::Assign { .. }, Stmt::Assign { .. })
            | (Stmt::If { .. }, Stmt::If { .. })
            | (Stmt::Match { .. }, Stmt::Match { .. })
            | (Stmt::While { .. }, Stmt::While { .. })
            | (Stmt::ForEach { .. }, Stmt::ForEach { .. })
            | (Stmt::ForRange { .. }, Stmt::ForRange { .. })
            | (Stmt::Break { .. }, Stmt::Break { .. })
            | (Stmt::Continue { .. }, Stmt::Continue { .. })
            | (Stmt::Return { .. }, Stmt::Return { .. })
            | (
                Stmt::Assert { .. } | Stmt::AssertEq { .. },
                Stmt::Assert { .. } | Stmt::AssertEq { .. }
            )
            | (Stmt::Expr { .. }, Stmt::Expr { .. })
    )
}

fn same_stmt_anchor(a: &Stmt, b: &Stmt) -> bool {
    match (a, b) {
        (Stmt::Let { name: n1, .. }, Stmt::Let { name: n2, .. }) => n1 == n2,
        (Stmt::Assign { target: t1, .. }, Stmt::Assign { target: t2, .. }) => t1 == t2,
        (Stmt::ForEach { var: v1, .. }, Stmt::ForEach { var: v2, .. }) => v1 == v2,
        (Stmt::ForRange { var: v1, .. }, Stmt::ForRange { var: v2, .. }) => v1 == v2,
        (Stmt::If { cond: c1, .. }, Stmt::If { cond: c2, .. }) => c1 == c2,
        (Stmt::Match { expr: e1, .. }, Stmt::Match { expr: e2, .. }) => e1 == e2,
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn merge_stmt_lists(
    base: &[Stmt],
    left: &[Stmt],
    right: &[Stmt],
    scope: &str,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> Vec<Stmt> {
    let b_to_l = align_stmts_to_base(base, left);
    let b_to_r = align_stmts_to_base(base, right);

    let mapped_l: HashSet<usize> = b_to_l.iter().filter_map(|&x| x).collect();
    let mapped_r: HashSet<usize> = b_to_r.iter().filter_map(|&x| x).collect();

    let mut out = Vec::new();
    let mut l_cur = 0usize;
    let mut r_cur = 0usize;

    for (b_idx, b_stmt) in base.iter().enumerate() {
        // Emit any unmapped Left / Right insertions strictly before this base anchor
        let l_stop = b_to_l[b_idx];
        let r_stop = b_to_r[b_idx];

        let mut pending_l_inserts = Vec::new();
        if let Some(ls) = l_stop {
            while l_cur < ls {
                if !mapped_l.contains(&l_cur) {
                    pending_l_inserts.push(left[l_cur].clone());
                }
                l_cur += 1;
            }
        }
        let mut pending_r_inserts = Vec::new();
        if let Some(rs) = r_stop {
            while r_cur < rs {
                if !mapped_r.contains(&r_cur) {
                    pending_r_inserts.push(right[r_cur].clone());
                }
                r_cur += 1;
            }
        }
        emit_concurrent_insertions(
            &pending_l_inserts,
            &pending_r_inserts,
            scope,
            left_spoke,
            right_spoke,
            &mut out,
            changes,
        );

        match (l_stop, r_stop) {
            (Some(li), Some(ri)) => {
                l_cur = l_cur.max(li + 1);
                r_cur = r_cur.max(ri + 1);
                let merged_s = merge_single_stmt_3way(
                    b_stmt,
                    &left[li],
                    &right[ri],
                    scope,
                    left_spoke,
                    right_spoke,
                    changes,
                    conflicts,
                );
                out.push(merged_s);
            }
            (None, Some(ri)) => {
                r_cur = r_cur.max(ri + 1);
                let r_stmt = &right[ri];
                if sem_eq_stmt(b_stmt, r_stmt) {
                    changes.push(AppliedChange {
                        spoke: left_spoke,
                        scope: scope.to_string(),
                        summary: format!("Deleted statement `{}`", summarize_stmt(b_stmt)),
                    });
                } else {
                    conflicts.push(MergeConflict {
                        node_id: stmt_id(b_stmt),
                        scope: scope.to_string(),
                        description: format!(
                            "Statement deleted in {} while modified in {}",
                            left_spoke.display_name(),
                            right_spoke.display_name()
                        ),
                        base_summary: summarize_stmt(b_stmt),
                        left_spoke,
                        left_summary: "(deleted)".to_string(),
                        right_spoke,
                        right_summary: summarize_stmt(r_stmt),
                    });
                    out.push(r_stmt.clone());
                }
            }
            (Some(li), None) => {
                l_cur = l_cur.max(li + 1);
                let l_stmt = &left[li];
                if sem_eq_stmt(b_stmt, l_stmt) {
                    changes.push(AppliedChange {
                        spoke: right_spoke,
                        scope: scope.to_string(),
                        summary: format!("Deleted statement `{}`", summarize_stmt(b_stmt)),
                    });
                } else {
                    conflicts.push(MergeConflict {
                        node_id: stmt_id(b_stmt),
                        scope: scope.to_string(),
                        description: format!(
                            "Statement modified in {} while deleted in {}",
                            left_spoke.display_name(),
                            right_spoke.display_name()
                        ),
                        base_summary: summarize_stmt(b_stmt),
                        left_spoke,
                        left_summary: summarize_stmt(l_stmt),
                        right_spoke,
                        right_summary: "(deleted)".to_string(),
                    });
                    out.push(l_stmt.clone());
                }
            }
            (None, None) => {
                changes.push(AppliedChange {
                    spoke: left_spoke,
                    scope: scope.to_string(),
                    summary: format!("Deleted statement `{}` (convergent)", summarize_stmt(b_stmt)),
                });
            }
        }
    }

    let mut tail_l = Vec::new();
    while l_cur < left.len() {
        if !mapped_l.contains(&l_cur) {
            tail_l.push(left[l_cur].clone());
        }
        l_cur += 1;
    }
    let mut tail_r = Vec::new();
    while r_cur < right.len() {
        if !mapped_r.contains(&r_cur) {
            tail_r.push(right[r_cur].clone());
        }
        r_cur += 1;
    }
    emit_concurrent_insertions(
        &tail_l,
        &tail_r,
        scope,
        left_spoke,
        right_spoke,
        &mut out,
        changes,
    );

    out
}

fn emit_concurrent_insertions(
    l_ins: &[Stmt],
    r_ins: &[Stmt],
    scope: &str,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    out: &mut Vec<Stmt>,
    changes: &mut Vec<AppliedChange>,
) {
    let mut used_r = vec![false; r_ins.len()];
    for ls in l_ins {
        if let Some((ri, _)) = r_ins
            .iter()
            .enumerate()
            .find(|(idx, rs)| !used_r[*idx] && sem_eq_stmt(ls, rs))
        {
            used_r[ri] = true;
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: scope.to_string(),
                summary: format!("Inserted `{}` (convergent)", summarize_stmt(ls)),
            });
        } else {
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: scope.to_string(),
                summary: format!("Inserted `{}`", summarize_stmt(ls)),
            });
        }
        out.push(ls.clone());
    }
    for (ri, rs) in r_ins.iter().enumerate() {
        if !used_r[ri] {
            changes.push(AppliedChange {
                spoke: right_spoke,
                scope: scope.to_string(),
                summary: format!("Inserted `{}`", summarize_stmt(rs)),
            });
            out.push(rs.clone());
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn merge_single_stmt_3way(
    base: &Stmt,
    left: &Stmt,
    right: &Stmt,
    scope: &str,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> Stmt {
    let l_same = sem_eq_stmt(base, left);
    let r_same = sem_eq_stmt(base, right);

    if l_same && r_same {
        return left.clone();
    }
    if !l_same && r_same {
        // Only Left modified this statement — if compound, describe inner changes or summary
        if !try_recurse_compound_only(
            base,
            left,
            right,
            scope,
            left_spoke,
            right_spoke,
            changes,
            conflicts,
        ) {
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: scope.to_string(),
                summary: format!(
                    "Modified `{}` -> `{}`",
                    summarize_stmt(base),
                    summarize_stmt(left)
                ),
            });
        }
        return left.clone();
    }
    if l_same && !r_same {
        if !try_recurse_compound_only(
            base,
            left,
            right,
            scope,
            left_spoke,
            right_spoke,
            changes,
            conflicts,
        ) {
            changes.push(AppliedChange {
                spoke: right_spoke,
                scope: scope.to_string(),
                summary: format!(
                    "Modified `{}` -> `{}`",
                    summarize_stmt(base),
                    summarize_stmt(right)
                ),
            });
        }
        return right.clone();
    }
    if sem_eq_stmt(left, right) {
        changes.push(AppliedChange {
            spoke: left_spoke,
            scope: scope.to_string(),
            summary: format!("Modified `{}` (convergent)", summarize_stmt(left)),
        });
        return left.clone();
    }

    // Both sides modified this statement differently — recurse into compound control flow!
    match (base, left, right) {
        (
            Stmt::If {
                id,
                cond: bc,
                then_body: bt,
                else_body: be,
                meta: bm,
            },
            Stmt::If {
                cond: lc,
                then_body: lt,
                else_body: le,
                meta: lm,
                ..
            },
            Stmt::If {
                cond: rc,
                then_body: rt,
                else_body: re,
                meta: rm,
                ..
            },
        ) => {
            let cond = merge_scalar_3way(
                bc,
                lc,
                rc,
                *id,
                scope,
                "if condition",
                summarize_expr,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let then_body = merge_stmt_lists(
                bt,
                lt,
                rt,
                &format!("{} [then]", scope),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let else_body = merge_stmt_lists(
                be,
                le,
                re,
                &format!("{} [else]", scope),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let meta = merge_meta_3way(
                bm,
                lm,
                rm,
                *id,
                scope,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            Stmt::If {
                id: *id,
                cond,
                then_body,
                else_body,
                meta,
            }
        }
        (
            Stmt::While {
                id,
                cond: bc,
                body: bb,
                meta: bm,
            },
            Stmt::While {
                cond: lc,
                body: lb,
                meta: lm,
                ..
            },
            Stmt::While {
                cond: rc,
                body: rb,
                meta: rm,
                ..
            },
        ) => {
            let cond = merge_scalar_3way(
                bc,
                lc,
                rc,
                *id,
                scope,
                "while condition",
                summarize_expr,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let body = merge_stmt_lists(
                bb,
                lb,
                rb,
                &format!("{} [while]", scope),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let meta = merge_meta_3way(
                bm,
                lm,
                rm,
                *id,
                scope,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            Stmt::While {
                id: *id,
                cond,
                body,
                meta,
            }
        }
        (
            Stmt::ForEach {
                id,
                var: bv,
                iter: bi,
                body: bb,
                meta: bm,
            },
            Stmt::ForEach {
                var: lv,
                iter: li,
                body: lb,
                meta: lm,
                ..
            },
            Stmt::ForEach {
                var: rv,
                iter: ri,
                body: rb,
                meta: rm,
                ..
            },
        ) => {
            let var = merge_scalar_3way(
                bv,
                lv,
                rv,
                *id,
                scope,
                "loop variable",
                |s| s.clone(),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let iter = merge_scalar_3way(
                bi,
                li,
                ri,
                *id,
                scope,
                "loop iterable",
                summarize_expr,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let body = merge_stmt_lists(
                bb,
                lb,
                rb,
                &format!("{} [for {}]", scope, var),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let meta = merge_meta_3way(
                bm,
                lm,
                rm,
                *id,
                scope,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            Stmt::ForEach {
                id: *id,
                var,
                iter,
                body,
                meta,
            }
        }
        (
            Stmt::ForRange {
                id,
                var: bv,
                start: bs,
                end: be,
                body: bb,
                meta: bm,
            },
            Stmt::ForRange {
                var: lv,
                start: ls,
                end: le,
                body: lb,
                meta: lm,
                ..
            },
            Stmt::ForRange {
                var: rv,
                start: rs,
                end: re,
                body: rb,
                meta: rm,
                ..
            },
        ) => {
            let var = merge_scalar_3way(
                bv,
                lv,
                rv,
                *id,
                scope,
                "range variable",
                |s| s.clone(),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let start = merge_scalar_3way(
                bs,
                ls,
                rs,
                *id,
                scope,
                "range start",
                summarize_expr,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let end = merge_scalar_3way(
                be,
                le,
                re,
                *id,
                scope,
                "range end",
                summarize_expr,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let body = merge_stmt_lists(
                bb,
                lb,
                rb,
                &format!("{} [range {}]", scope, var),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let meta = merge_meta_3way(
                bm,
                lm,
                rm,
                *id,
                scope,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            Stmt::ForRange {
                id: *id,
                var,
                start,
                end,
                body,
                meta,
            }
        }
        (
            Stmt::Match {
                id,
                expr: be,
                arms: ba,
                meta: bm,
            },
            Stmt::Match {
                expr: le,
                arms: la,
                meta: lm,
                ..
            },
            Stmt::Match {
                expr: re,
                arms: ra,
                meta: rm,
                ..
            },
        ) => {
            let expr = merge_scalar_3way(
                be,
                le,
                re,
                *id,
                scope,
                "match scrutinee",
                summarize_expr,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let arms = merge_match_arms_3way(
                ba,
                la,
                ra,
                *id,
                scope,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let meta = merge_meta_3way(
                bm,
                lm,
                rm,
                *id,
                scope,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            Stmt::Match {
                id: *id,
                expr,
                arms,
                meta,
            }
        }
        _ => {
            conflicts.push(MergeConflict {
                node_id: stmt_id(base),
                scope: scope.to_string(),
                description: format!(
                    "Conflicting edits to statement in {} ({} vs {})",
                    scope,
                    left_spoke.display_name(),
                    right_spoke.display_name()
                ),
                base_summary: summarize_stmt(base),
                left_spoke,
                left_summary: summarize_stmt(left),
                right_spoke,
                right_summary: summarize_stmt(right),
            });
            left.clone()
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn try_recurse_compound_only(
    base: &Stmt,
    left: &Stmt,
    right: &Stmt,
    scope: &str,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> bool {
    if matches!(
        base,
        Stmt::If { .. }
            | Stmt::While { .. }
            | Stmt::ForEach { .. }
            | Stmt::ForRange { .. }
            | Stmt::Match { .. }
    ) && same_stmt_family(base, left)
        && same_stmt_family(base, right)
    {
        let before_len = changes.len();
        let _ = merge_compound_for_log(
            base,
            left,
            right,
            scope,
            left_spoke,
            right_spoke,
            changes,
            conflicts,
        );
        return changes.len() > before_len;
    }
    false
}

#[allow(clippy::too_many_arguments)]
fn merge_compound_for_log(
    base: &Stmt,
    left: &Stmt,
    right: &Stmt,
    scope: &str,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) {
    match (base, left, right) {
        (
            Stmt::If {
                id,
                cond: bc,
                then_body: bt,
                else_body: be,
                ..
            },
            Stmt::If {
                cond: lc,
                then_body: lt,
                else_body: le,
                ..
            },
            Stmt::If {
                cond: rc,
                then_body: rt,
                else_body: re,
                ..
            },
        ) => {
            let _ = merge_scalar_3way(
                bc,
                lc,
                rc,
                *id,
                scope,
                "if condition",
                summarize_expr,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let _ = merge_stmt_lists(
                bt,
                lt,
                rt,
                &format!("{} [then]", scope),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let _ = merge_stmt_lists(
                be,
                le,
                re,
                &format!("{} [else]", scope),
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
        }
        (
            Stmt::Match {
                id,
                expr: be,
                arms: ba,
                ..
            },
            Stmt::Match {
                expr: le, arms: la, ..
            },
            Stmt::Match {
                expr: re, arms: ra, ..
            },
        ) => {
            let _ = merge_scalar_3way(
                be,
                le,
                re,
                *id,
                scope,
                "match scrutinee",
                summarize_expr,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
            let _ = merge_match_arms_3way(
                ba,
                la,
                ra,
                *id,
                scope,
                left_spoke,
                right_spoke,
                changes,
                conflicts,
            );
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn merge_match_arms_3way(
    base: &[MatchArm],
    left: &[MatchArm],
    right: &[MatchArm],
    match_id: NodeId,
    scope: &str,
    left_spoke: SpokeId,
    right_spoke: SpokeId,
    changes: &mut Vec<AppliedChange>,
    conflicts: &mut Vec<MergeConflict>,
) -> Vec<MatchArm> {
    let mut out = Vec::new();
    let mut used_l = vec![false; left.len()];
    let mut used_r = vec![false; right.len()];

    for b_arm in base {
        let li = left
            .iter()
            .enumerate()
            .find(|(idx, a)| !used_l[*idx] && a.pat == b_arm.pat)
            .map(|(i, _)| i);
        let ri = right
            .iter()
            .enumerate()
            .find(|(idx, a)| !used_r[*idx] && a.pat == b_arm.pat)
            .map(|(i, _)| i);

        if let Some(i) = li {
            used_l[i] = true;
        }
        if let Some(i) = ri {
            used_r[i] = true;
        }

        let pat_lbl = summarize_pat(&b_arm.pat);
        let arm_scope = format!("{} [case {}]", scope, pat_lbl);

        match (li, ri) {
            (Some(l_idx), Some(r_idx)) => {
                let merged_body = merge_stmt_lists(
                    &b_arm.body,
                    &left[l_idx].body,
                    &right[r_idx].body,
                    &arm_scope,
                    left_spoke,
                    right_spoke,
                    changes,
                    conflicts,
                );
                out.push(MatchArm {
                    pat: b_arm.pat.clone(),
                    body: merged_body,
                });
            }
            (None, Some(r_idx)) => {
                if sem_eq_stmts(&b_arm.body, &right[r_idx].body) {
                    changes.push(AppliedChange {
                        spoke: left_spoke,
                        scope: scope.to_string(),
                        summary: format!("Removed match arm `{}`", pat_lbl),
                    });
                } else {
                    conflicts.push(MergeConflict {
                        node_id: match_id,
                        scope: arm_scope,
                        description: format!("Match arm `{}` deleted vs modified", pat_lbl),
                        base_summary: summarize_block(&b_arm.body),
                        left_spoke,
                        left_summary: "(deleted)".to_string(),
                        right_spoke,
                        right_summary: summarize_block(&right[r_idx].body),
                    });
                    out.push(right[r_idx].clone());
                }
            }
            (Some(l_idx), None) => {
                if sem_eq_stmts(&b_arm.body, &left[l_idx].body) {
                    changes.push(AppliedChange {
                        spoke: right_spoke,
                        scope: scope.to_string(),
                        summary: format!("Removed match arm `{}`", pat_lbl),
                    });
                } else {
                    conflicts.push(MergeConflict {
                        node_id: match_id,
                        scope: arm_scope,
                        description: format!("Match arm `{}` modified vs deleted", pat_lbl),
                        base_summary: summarize_block(&b_arm.body),
                        left_spoke,
                        left_summary: summarize_block(&left[l_idx].body),
                        right_spoke,
                        right_summary: "(deleted)".to_string(),
                    });
                    out.push(left[l_idx].clone());
                }
            }
            (None, None) => {}
        }
    }

    // Newly added arms (keep Wildcard `_` last if present!)
    let mut wild_arm: Option<MatchArm> = None;
    if let Some(pos) = out.iter().position(|a| a.pat == MatchPat::Wildcard) {
        wild_arm = Some(out.remove(pos));
    }

    for (i, la) in left.iter().enumerate() {
        if !used_l[i] {
            let pat_lbl = summarize_pat(&la.pat);
            if let Some((ri, ra)) = right
                .iter()
                .enumerate()
                .find(|(idx, ra)| !used_r[*idx] && ra.pat == la.pat)
            {
                used_r[ri] = true;
                if !sem_eq_stmts(&la.body, &ra.body) {
                    conflicts.push(MergeConflict {
                        node_id: match_id,
                        scope: format!("{} [case {}]", scope, pat_lbl),
                        description: format!("Conflicting new match arm `{}`", pat_lbl),
                        base_summary: "(none)".to_string(),
                        left_spoke,
                        left_summary: summarize_block(&la.body),
                        right_spoke,
                        right_summary: summarize_block(&ra.body),
                    });
                }
            }
            changes.push(AppliedChange {
                spoke: left_spoke,
                scope: scope.to_string(),
                summary: format!("Added match arm `{}`", pat_lbl),
            });
            out.push(la.clone());
        }
    }
    for (i, ra) in right.iter().enumerate() {
        if !used_r[i] {
            let pat_lbl = summarize_pat(&ra.pat);
            changes.push(AppliedChange {
                spoke: right_spoke,
                scope: scope.to_string(),
                summary: format!("Added match arm `{}`", pat_lbl),
            });
            out.push(ra.clone());
        }
    }

    if let Some(w) = wild_arm {
        out.push(w);
    }
    out
}

// ============================================================================
// Pairwise Diff Helpers & Semantic Equality (Ignoring Transient NodeIds)
// ============================================================================

fn diff_item_pair(old_item: &Item, new_item: &Item, deltas: &mut Vec<SemanticDelta>) {
    let scope = item_key(new_item);
    match (old_item, new_item) {
        (Item::Enum(oe), Item::Enum(ne)) => {
            if oe.name != ne.name {
                deltas.push(SemanticDelta {
                    kind: "modified",
                    scope: scope.clone(),
                    summary: format!("Renamed enum {} -> {}", oe.name, ne.name),
                });
            }
            if oe.variants != ne.variants {
                deltas.push(SemanticDelta {
                    kind: "modified",
                    scope: scope.clone(),
                    summary: format!("Variants: {:?} -> {:?}", oe.variants, ne.variants),
                });
            }
            if oe.meta != ne.meta {
                deltas.push(SemanticDelta {
                    kind: "metadata",
                    scope,
                    summary: format!("Updated enum metadata: {:?}", ne.meta),
                });
            }
        }
        (Item::Struct(os), Item::Struct(ns)) => {
            if os.name != ns.name {
                deltas.push(SemanticDelta {
                    kind: "modified",
                    scope: scope.clone(),
                    summary: format!("Renamed struct {} -> {}", os.name, ns.name),
                });
            }
            let of: Vec<String> = os
                .fields
                .iter()
                .map(|f| format!("{}: {}", f.name, f.ty.display()))
                .collect();
            let nf: Vec<String> = ns
                .fields
                .iter()
                .map(|f| format!("{}: {}", f.name, f.ty.display()))
                .collect();
            if of != nf {
                deltas.push(SemanticDelta {
                    kind: "modified",
                    scope: scope.clone(),
                    summary: format!("Fields: [{}] -> [{}]", of.join(", "), nf.join(", ")),
                });
            }
            if os.meta != ns.meta {
                deltas.push(SemanticDelta {
                    kind: "metadata",
                    scope,
                    summary: format!("Updated struct metadata: {:?}", ns.meta),
                });
            }
        }
        (Item::Function(of), Item::Function(nf)) => {
            if of.name != nf.name || of.ret_ty != nf.ret_ty || !sem_eq_params(&of.params, &nf.params)
            {
                deltas.push(SemanticDelta {
                    kind: "modified",
                    scope: scope.clone(),
                    summary: format!(
                        "Signature: fn {}({}) -> {}  =>  fn {}({}) -> {}",
                        of.name,
                        fmt_params(&of.params),
                        of.ret_ty.display(),
                        nf.name,
                        fmt_params(&nf.params),
                        nf.ret_ty.display()
                    ),
                });
            }
            for (op, np) in of.params.iter().zip(nf.params.iter()) {
                if op.meta != np.meta {
                    deltas.push(SemanticDelta {
                        kind: "metadata",
                        scope: format!("{}::{}", scope, np.name),
                        summary: format!("Parameter metadata: {:?} -> {:?}", op.meta, np.meta),
                    });
                }
            }
            diff_stmt_lists(&of.body, &nf.body, &scope, deltas);
        }
        (Item::Test(ot), Item::Test(nt)) => {
            diff_stmt_lists(&ot.body, &nt.body, &scope, deltas);
        }
        _ => {}
    }
}

fn diff_stmt_lists(old_s: &[Stmt], new_s: &[Stmt], scope: &str, deltas: &mut Vec<SemanticDelta>) {
    let mapping = align_stmts_to_base(old_s, new_s);
    let mapped_new: HashSet<usize> = mapping.iter().filter_map(|&x| x).collect();

    for (bi, bs) in old_s.iter().enumerate() {
        match mapping[bi] {
            None => deltas.push(SemanticDelta {
                kind: "removed",
                scope: scope.to_string(),
                summary: format!("Removed `{}`", summarize_stmt(bs)),
            }),
            Some(ni) => {
                let ns = &new_s[ni];
                if !sem_eq_stmt(bs, ns) {
                    match (bs, ns) {
                        (
                            Stmt::If {
                                cond: c1,
                                then_body: t1,
                                else_body: e1,
                                ..
                            },
                            Stmt::If {
                                cond: c2,
                                then_body: t2,
                                else_body: e2,
                                ..
                            },
                        ) => {
                            if c1 != c2 {
                                deltas.push(SemanticDelta {
                                    kind: "modified",
                                    scope: scope.to_string(),
                                    summary: format!(
                                        "If condition: `{}` -> `{}`",
                                        summarize_expr(c1),
                                        summarize_expr(c2)
                                    ),
                                });
                            }
                            diff_stmt_lists(t1, t2, &format!("{} [then]", scope), deltas);
                            diff_stmt_lists(e1, e2, &format!("{} [else]", scope), deltas);
                        }
                        _ => deltas.push(SemanticDelta {
                            kind: "modified",
                            scope: scope.to_string(),
                            summary: format!(
                                "`{}` -> `{}`",
                                summarize_stmt(bs),
                                summarize_stmt(ns)
                            ),
                        }),
                    }
                }
            }
        }
    }

    for (ni, ns) in new_s.iter().enumerate() {
        if !mapped_new.contains(&ni) {
            deltas.push(SemanticDelta {
                kind: "added",
                scope: scope.to_string(),
                summary: format!("Added `{}`", summarize_stmt(ns)),
            });
        }
    }
}

fn sem_eq_item(a: &Item, b: &Item) -> bool {
    match (a, b) {
        (Item::Enum(e1), Item::Enum(e2)) => {
            e1.name == e2.name
                && e1.variants == e2.variants
                && e1.comments == e2.comments
                && e1.meta == e2.meta
        }
        (Item::Struct(s1), Item::Struct(s2)) => {
            s1.name == s2.name
                && s1.comments == s2.comments
                && s1.meta == s2.meta
                && s1.fields.len() == s2.fields.len()
                && s1
                    .fields
                    .iter()
                    .zip(&s2.fields)
                    .all(|(f1, f2)| f1.name == f2.name && f1.ty == f2.ty && f1.meta == f2.meta)
        }
        (Item::Function(f1), Item::Function(f2)) => {
            f1.name == f2.name
                && f1.ret_ty == f2.ret_ty
                && f1.comments == f2.comments
                && f1.meta == f2.meta
                && sem_eq_params(&f1.params, &f2.params)
                && f1
                    .params
                    .iter()
                    .zip(&f2.params)
                    .all(|(p1, p2)| p1.meta == p2.meta)
                && sem_eq_stmts(&f1.body, &f2.body)
        }
        (Item::Test(t1), Item::Test(t2)) => {
            t1.name == t2.name
                && t1.comments == t2.comments
                && t1.meta == t2.meta
                && sem_eq_stmts(&t1.body, &t2.body)
        }
        _ => false,
    }
}

fn sem_eq_params(a: &[Param], b: &[Param]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|(p1, p2)| p1.name == p2.name && p1.ty == p2.ty)
}

fn sem_eq_stmts(a: &[Stmt], b: &[Stmt]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(s1, s2)| sem_eq_stmt(s1, s2))
}

fn sem_eq_stmt(a: &Stmt, b: &Stmt) -> bool {
    match (a, b) {
        (Stmt::Comment { text: t1, .. }, Stmt::Comment { text: t2, .. }) => t1 == t2,
        (
            Stmt::Let {
                name: n1,
                mutable: m1,
                ty: ty1,
                value: v1,
                meta: mt1,
                ..
            },
            Stmt::Let {
                name: n2,
                mutable: m2,
                ty: ty2,
                value: v2,
                meta: mt2,
                ..
            },
        ) => n1 == n2 && m1 == m2 && ty1 == ty2 && v1 == v2 && mt1 == mt2,
        (
            Stmt::Assign {
                target: t1,
                op: o1,
                value: v1,
                meta: mt1,
                ..
            },
            Stmt::Assign {
                target: t2,
                op: o2,
                value: v2,
                meta: mt2,
                ..
            },
        ) => t1 == t2 && o1 == o2 && v1 == v2 && mt1 == mt2,
        (
            Stmt::If {
                cond: c1,
                then_body: tb1,
                else_body: eb1,
                meta: mt1,
                ..
            },
            Stmt::If {
                cond: c2,
                then_body: tb2,
                else_body: eb2,
                meta: mt2,
                ..
            },
        ) => c1 == c2 && mt1 == mt2 && sem_eq_stmts(tb1, tb2) && sem_eq_stmts(eb1, eb2),
        (
            Stmt::Match {
                expr: e1,
                arms: a1,
                meta: mt1,
                ..
            },
            Stmt::Match {
                expr: e2,
                arms: a2,
                meta: mt2,
                ..
            },
        ) => {
            e1 == e2
                && mt1 == mt2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2)
                    .all(|(x, y)| x.pat == y.pat && sem_eq_stmts(&x.body, &y.body))
        }
        (
            Stmt::While {
                cond: c1,
                body: b1,
                meta: mt1,
                ..
            },
            Stmt::While {
                cond: c2,
                body: b2,
                meta: mt2,
                ..
            },
        ) => c1 == c2 && mt1 == mt2 && sem_eq_stmts(b1, b2),
        (
            Stmt::ForEach {
                var: v1,
                iter: i1,
                body: b1,
                meta: mt1,
                ..
            },
            Stmt::ForEach {
                var: v2,
                iter: i2,
                body: b2,
                meta: mt2,
                ..
            },
        ) => v1 == v2 && i1 == i2 && mt1 == mt2 && sem_eq_stmts(b1, b2),
        (
            Stmt::ForRange {
                var: v1,
                start: s1,
                end: e1,
                body: b1,
                meta: mt1,
                ..
            },
            Stmt::ForRange {
                var: v2,
                start: s2,
                end: e2,
                body: b2,
                meta: mt2,
                ..
            },
        ) => v1 == v2 && s1 == s2 && e1 == e2 && mt1 == mt2 && sem_eq_stmts(b1, b2),
        (Stmt::Break { .. }, Stmt::Break { .. }) => true,
        (Stmt::Continue { .. }, Stmt::Continue { .. }) => true,
        (
            Stmt::Return {
                value: v1,
                meta: mt1,
                ..
            },
            Stmt::Return {
                value: v2,
                meta: mt2,
                ..
            },
        ) => v1 == v2 && mt1 == mt2,
        (
            Stmt::Assert {
                cond: c1,
                meta: mt1,
                ..
            },
            Stmt::Assert {
                cond: c2,
                meta: mt2,
                ..
            },
        ) => c1 == c2 && mt1 == mt2,
        (
            Stmt::AssertEq {
                left: l1,
                right: r1,
                meta: mt1,
                ..
            },
            Stmt::AssertEq {
                left: l2,
                right: r2,
                meta: mt2,
                ..
            },
        ) => l1 == l2 && r1 == r2 && mt1 == mt2,
        (
            Stmt::Expr {
                expr: e1,
                meta: mt1,
                ..
            },
            Stmt::Expr {
                expr: e2,
                meta: mt2,
                ..
            },
        ) => e1 == e2 && mt1 == mt2,
        _ => false,
    }
}

fn stmt_id(s: &Stmt) -> NodeId {
    match s {
        Stmt::Comment { id, .. }
        | Stmt::Let { id, .. }
        | Stmt::Assign { id, .. }
        | Stmt::If { id, .. }
        | Stmt::Match { id, .. }
        | Stmt::While { id, .. }
        | Stmt::ForEach { id, .. }
        | Stmt::ForRange { id, .. }
        | Stmt::Break { id }
        | Stmt::Continue { id }
        | Stmt::Return { id, .. }
        | Stmt::Assert { id, .. }
        | Stmt::AssertEq { id, .. }
        | Stmt::Expr { id, .. } => *id,
    }
}

fn fmt_params(params: &[Param]) -> String {
    params
        .iter()
        .map(|p| format!("{}: {}", p.name, p.ty.display()))
        .collect::<Vec<_>>()
        .join(", ")
}

fn summarize_pat(pat: &MatchPat) -> String {
    match pat {
        MatchPat::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
        MatchPat::Int(v) => v.to_string(),
        MatchPat::Str(s) => format!("{:?}", s),
        MatchPat::Wildcard => "_".to_string(),
    }
}

fn summarize_block(stmts: &[Stmt]) -> String {
    stmts
        .iter()
        .map(summarize_stmt)
        .collect::<Vec<_>>()
        .join("; ")
}

fn summarize_stmt(s: &Stmt) -> String {
    match s {
        Stmt::Comment { text, .. } => format!("// {}", text),
        Stmt::Let {
            name,
            mutable,
            value,
            ..
        } => {
            let kw = if *mutable { "let mut" } else { "let" };
            format!("{} {} = {}", kw, name, summarize_expr(value))
        }
        Stmt::Assign {
            target, op, value, ..
        } => {
            let tgt = match target {
                AssignTarget::Var(v) => v.clone(),
                AssignTarget::Field { base, field } => format!("{}.{}", base, field),
                AssignTarget::Index { base, index } => {
                    format!("{}[{}]", base, summarize_expr(index))
                }
            };
            let op_s = match op {
                AssignOp::Set => "=",
                AssignOp::AddAssign => "+=",
                AssignOp::SubAssign => "-=",
            };
            format!("{} {} {}", tgt, op_s, summarize_expr(value))
        }
        Stmt::If { cond, .. } => format!("if ({}) {{ ... }}", summarize_expr(cond)),
        Stmt::Match { expr, arms, .. } => {
            format!("match ({}) [{} arms]", summarize_expr(expr), arms.len())
        }
        Stmt::While { cond, .. } => format!("while ({}) {{ ... }}", summarize_expr(cond)),
        Stmt::ForEach { var, iter, .. } => {
            format!("for {} in {} {{ ... }}", var, summarize_expr(iter))
        }
        Stmt::ForRange {
            var, start, end, ..
        } => format!(
            "for {} in {}..{} {{ ... }}",
            var,
            summarize_expr(start),
            summarize_expr(end)
        ),
        Stmt::Break { .. } => "break".to_string(),
        Stmt::Continue { .. } => "continue".to_string(),
        Stmt::Return { value: Some(v), .. } => format!("return {}", summarize_expr(v)),
        Stmt::Return { value: None, .. } => "return".to_string(),
        Stmt::Assert { cond, .. } => format!("assert({})", summarize_expr(cond)),
        Stmt::AssertEq { left, right, .. } => {
            format!("assert_eq({}, {})", summarize_expr(left), summarize_expr(right))
        }
        Stmt::Expr { expr, .. } => summarize_expr(expr),
    }
}

fn summarize_expr(e: &Expr) -> String {
    match e {
        Expr::Int(v) => v.to_string(),
        Expr::Float(v) => format!("{}", v),
        Expr::Bool(b) => b.to_string(),
        Expr::Str(s) => format!("{:?}", s),
        Expr::Var(v) => v.clone(),
        Expr::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
        Expr::List(items) => {
            let inner: Vec<String> = items.iter().map(summarize_expr).collect();
            format!("[{}]", inner.join(", "))
        }
        Expr::StructInit { name, fields } => {
            let fs: Vec<String> = fields
                .iter()
                .map(|(k, v)| format!("{}: {}", k, summarize_expr(v)))
                .collect();
            format!("{} {{ {} }}", name, fs.join(", "))
        }
        Expr::FieldAccess { base, field } => format!("{}.{}", summarize_expr(base), field),
        Expr::Index { base, index } => {
            format!("{}[{}]", summarize_expr(base), summarize_expr(index))
        }
        Expr::Unary { op, expr: inner } => match op {
            UnaryOp::Neg => format!("-{}", summarize_expr(inner)),
            UnaryOp::Not => format!("!{}", summarize_expr(inner)),
        },
        Expr::Binary { op, left, right } => {
            let op_s = match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "/",
                BinOp::IntDiv => "//",
                BinOp::Mod => "%",
                BinOp::Eq => "==",
                BinOp::Ne => "!=",
                BinOp::Lt => "<",
                BinOp::Le => "<=",
                BinOp::Gt => ">",
                BinOp::Ge => ">=",
                BinOp::And => "&&",
                BinOp::Or => "||",
            };
            format!("({} {} {})", summarize_expr(left), op_s, summarize_expr(right))
        }
        Expr::Call { func, args } => {
            let as_: Vec<String> = args.iter().map(summarize_expr).collect();
            format!("{}({})", func, as_.join(", "))
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(x) => format!("len({})", summarize_expr(x)),
            Intrinsic::Min(a, b) => format!("min({}, {})", summarize_expr(a), summarize_expr(b)),
            Intrinsic::Max(a, b) => format!("max({}, {})", summarize_expr(a), summarize_expr(b)),
            Intrinsic::Abs(a) => format!("abs({})", summarize_expr(a)),
            Intrinsic::Push { list, value } => {
                format!("push({}, {})", summarize_expr(list), summarize_expr(value))
            }
            Intrinsic::Print(args) => {
                let as_: Vec<String> = args.iter().map(summarize_expr).collect();
                format!("print({})", as_.join(", "))
            }
            Intrinsic::Contains { haystack, needle } => format!(
                "contains({}, {})",
                summarize_expr(haystack),
                summarize_expr(needle)
            ),
            Intrinsic::Upper(x) => format!("upper({})", summarize_expr(x)),
            Intrinsic::Lower(x) => format!("lower({})", summarize_expr(x)),
            Intrinsic::ToStr(x) => format!("str({})", summarize_expr(x)),
        },
    }
}

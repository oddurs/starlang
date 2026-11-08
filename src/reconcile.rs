use std::collections::HashSet;

use crate::hub::{
    normalize_module, AssignOp, AssignTarget, BinOp, EnumDecl, Expr, Field, FnDecl, HubModule,
    Item, Metadata, NodeId, Param, Stmt, StructDecl, TestDecl, Type,
};
use crate::lens::SpokeId;

pub fn reconcile_modules(
    mut parsed: HubModule,
    prev: &HubModule,
    edited_spoke: SpokeId,
) -> HubModule {
    let mut next_id = prev.next_id.max(1);
    let mut used_ids = HashSet::new();

    let prev_structs: Vec<&StructDecl> = prev
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Struct(s) => Some(s),
            _ => None,
        })
        .collect();
    let prev_enums: Vec<&EnumDecl> = prev
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Enum(e) => Some(e),
            _ => None,
        })
        .collect();
    let prev_fns: Vec<&FnDecl> = prev
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Function(f) => Some(f),
            _ => None,
        })
        .collect();
    let prev_tests: Vec<&TestDecl> = prev
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Test(t) => Some(t),
            _ => None,
        })
        .collect();

    let mut matched_prev_structs = vec![false; prev_structs.len()];
    let mut matched_prev_enums = vec![false; prev_enums.len()];
    let mut matched_prev_fns = vec![false; prev_fns.len()];
    let mut matched_prev_tests = vec![false; prev_tests.len()];

    let mut struct_matches: Vec<Option<usize>> = Vec::new();
    let mut enum_matches: Vec<Option<usize>> = Vec::new();
    let mut fn_matches: Vec<Option<usize>> = Vec::new();
    let mut test_matches: Vec<Option<usize>> = Vec::new();

    for item in &parsed.items {
        match item {
            Item::Struct(s) => {
                let found = prev_structs
                    .iter()
                    .enumerate()
                    .find(|(idx, ps)| !matched_prev_structs[*idx] && ps.name == s.name)
                    .map(|(idx, _)| idx);
                if let Some(idx) = found {
                    matched_prev_structs[idx] = true;
                }
                struct_matches.push(found);
            }
            Item::Enum(e) => {
                let found = prev_enums
                    .iter()
                    .enumerate()
                    .find(|(idx, pe)| !matched_prev_enums[*idx] && pe.name == e.name)
                    .map(|(idx, _)| idx);
                if let Some(idx) = found {
                    matched_prev_enums[idx] = true;
                }
                enum_matches.push(found);
            }
            Item::Function(f) => {
                let found = prev_fns
                    .iter()
                    .enumerate()
                    .find(|(idx, pf)| !matched_prev_fns[*idx] && pf.name == f.name)
                    .map(|(idx, _)| idx);
                if let Some(idx) = found {
                    matched_prev_fns[idx] = true;
                }
                fn_matches.push(found);
            }
            Item::Test(t) => {
                let canon = t.name.strip_prefix("test_").unwrap_or(t.name.as_str());
                let found = prev_tests
                    .iter()
                    .enumerate()
                    .find(|(idx, pt)| !matched_prev_tests[*idx] && pt.name == canon)
                    .map(|(idx, _)| idx);
                if let Some(idx) = found {
                    matched_prev_tests[idx] = true;
                }
                test_matches.push(found);
            }
        }
    }

    // Positional fallback for single-item renames
    let parsed_structs: Vec<&StructDecl> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Struct(s) => Some(s),
            _ => None,
        })
        .collect();
    for (s_ord, m_slot) in struct_matches.iter_mut().enumerate() {
        if m_slot.is_none() && s_ord < prev_structs.len() && !matched_prev_structs[s_ord]
            && parsed_structs[s_ord].fields.len() == prev_structs[s_ord].fields.len() {
                matched_prev_structs[s_ord] = true;
                *m_slot = Some(s_ord);
            }
    }

    let parsed_enums: Vec<&EnumDecl> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Enum(e) => Some(e),
            _ => None,
        })
        .collect();
    for (e_ord, m_slot) in enum_matches.iter_mut().enumerate() {
        if m_slot.is_none() && e_ord < prev_enums.len() && !matched_prev_enums[e_ord]
            && parsed_enums[e_ord].variants.len() == prev_enums[e_ord].variants.len() {
                matched_prev_enums[e_ord] = true;
                *m_slot = Some(e_ord);
            }
    }

    let parsed_fns: Vec<&FnDecl> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Function(f) => Some(f),
            _ => None,
        })
        .collect();
    for (f_ord, m_slot) in fn_matches.iter_mut().enumerate() {
        if m_slot.is_none() && f_ord < prev_fns.len() && !matched_prev_fns[f_ord]
            && parsed_fns[f_ord].params.len() == prev_fns[f_ord].params.len() {
                matched_prev_fns[f_ord] = true;
                *m_slot = Some(f_ord);
            }
    }

    for (t_ord, m_slot) in test_matches.iter_mut().enumerate() {
        if m_slot.is_none() && t_ord < prev_tests.len() && !matched_prev_tests[t_ord] {
            matched_prev_tests[t_ord] = true;
            *m_slot = Some(t_ord);
        }
    }

    let prev_enum_names: HashSet<&str> = prev_enums.iter().map(|e| e.name.as_str()).collect();
    let cur_enum_names: HashSet<String> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Enum(e) => Some(e.name.clone()),
            _ => None,
        })
        .collect();

    let mut s_cursor = 0;
    let mut e_cursor = 0;
    let mut f_cursor = 0;
    let mut t_cursor = 0;

    for item in &mut parsed.items {
        match item {
            Item::Struct(s) => {
                let prev_s = struct_matches[s_cursor].map(|idx| prev_structs[idx]);
                s_cursor += 1;
                reconcile_struct(s, prev_s, edited_spoke, &mut next_id, &mut used_ids);
            }
            Item::Enum(e) => {
                let prev_e = enum_matches[e_cursor].map(|idx| prev_enums[idx]);
                e_cursor += 1;
                e.id = claim_id(prev_e.map(|p| p.id), &mut next_id, &mut used_ids);
                e.meta = merge_meta(&e.meta, prev_e.map(|p| &p.meta), edited_spoke);
            }
            Item::Function(f) => {
                let prev_f = fn_matches[f_cursor].map(|idx| prev_fns[idx]);
                f_cursor += 1;
                reconcile_fn(
                    f,
                    prev_f,
                    edited_spoke,
                    &cur_enum_names,
                    &prev_enum_names,
                    &mut next_id,
                    &mut used_ids,
                );
            }
            Item::Test(t) => {
                let prev_t = test_matches[t_cursor].map(|idx| prev_tests[idx]);
                t_cursor += 1;
                t.id = claim_id(prev_t.map(|p| p.id), &mut next_id, &mut used_ids);
                t.meta = merge_meta(&t.meta, prev_t.map(|p| &p.meta), edited_spoke);
                let prev_body = prev_t.map(|p| p.body.as_slice()).unwrap_or(&[]);
                reconcile_stmts(&mut t.body, prev_body, edited_spoke, &mut next_id, &mut used_ids);
            }
        }
    }

    parsed.next_id = next_id;
    normalize_module(&mut parsed);
    parsed
}

fn claim_id(preferred: Option<NodeId>, next_id: &mut NodeId, used: &mut HashSet<NodeId>) -> NodeId {
    if let Some(id) = preferred {
        if id > 0 && !used.contains(&id) {
            used.insert(id);
            if id >= *next_id {
                *next_id = id + 1;
            }
            return id;
        }
    }
    while used.contains(next_id) {
        *next_id += 1;
    }
    let id = *next_id;
    used.insert(id);
    *next_id += 1;
    id
}

fn merge_meta(new_meta: &Metadata, prev_meta: Option<&Metadata>, edited_spoke: SpokeId) -> Metadata {
    let Some(prev) = prev_meta else {
        return new_meta.clone();
    };
    let Some(owned_prefix) = edited_spoke.meta_prefix() else {
        return new_meta.clone();
    };

    let mut merged = Metadata::new();
    for (k, v) in prev {
        if (!k.starts_with(owned_prefix) && k != "explicit_mut")
            || (k == "explicit_mut"
                && matches!(
                    edited_spoke,
                    SpokeId::Python
                        | SpokeId::Go
                        | SpokeId::Ruby
                        | SpokeId::Lua
                        | SpokeId::Perl
                        | SpokeId::C
                        | SpokeId::Java
                ))
        {
            merged.insert(k.clone(), v.clone());
        }
    }
    for (k, v) in new_meta {
        merged.insert(k.clone(), v.clone());
    }
    merged
}

fn prune_incompatible_param_meta(
    meta: &mut Metadata,
    ty: &Type,
    cur_enums: &HashSet<String>,
) {
    if let Some(pass) = meta.get("rust.pass") {
        let valid = match pass.as_str() {
            "slice" => matches!(ty, Type::List(_)),
            "ref" => match ty {
                Type::Str => true,
                Type::Named(n) => !cur_enums.contains(n),
                _ => false,
            },
            "owned" => true,
            _ => true,
        };
        if !valid {
            meta.remove("rust.pass");
        }
    }
    if meta.contains_key("cpp.pass") {
        let valid = match ty {
            Type::List(_) | Type::Str => true,
            Type::Named(n) => !cur_enums.contains(n),
            _ => false,
        };
        if !valid {
            meta.remove("cpp.pass");
        }
    }
}

fn reconcile_struct(
    s: &mut StructDecl,
    prev: Option<&StructDecl>,
    edited_spoke: SpokeId,
    next_id: &mut NodeId,
    used: &mut HashSet<NodeId>,
) {
    s.id = claim_id(prev.map(|p| p.id), next_id, used);
    s.meta = merge_meta(&s.meta, prev.map(|p| &p.meta), edited_spoke);

    let prev_fields: &[Field] = prev.map(|p| p.fields.as_slice()).unwrap_or(&[]);
    let mut matched = vec![false; prev_fields.len()];

    for (idx, field) in s.fields.iter_mut().enumerate() {
        let found = prev_fields
            .iter()
            .enumerate()
            .find(|(i, pf)| !matched[*i] && pf.name == field.name)
            .or_else(|| {
                if idx < prev_fields.len() && !matched[idx] && prev_fields[idx].ty == field.ty {
                    Some((idx, &prev_fields[idx]))
                } else {
                    None
                }
            });

        if let Some((i, pf)) = found {
            matched[i] = true;
            field.id = claim_id(Some(pf.id), next_id, used);
            field.meta = merge_meta(&field.meta, Some(&pf.meta), edited_spoke);
        } else {
            field.id = claim_id(None, next_id, used);
        }
    }
}

fn reconcile_fn(
    f: &mut FnDecl,
    prev: Option<&FnDecl>,
    edited_spoke: SpokeId,
    cur_enums: &HashSet<String>,
    _prev_enums: &HashSet<&str>,
    next_id: &mut NodeId,
    used: &mut HashSet<NodeId>,
) {
    f.id = claim_id(prev.map(|p| p.id), next_id, used);
    f.meta = merge_meta(&f.meta, prev.map(|p| &p.meta), edited_spoke);

    let prev_params: &[Param] = prev.map(|p| p.params.as_slice()).unwrap_or(&[]);
    let mut matched = vec![false; prev_params.len()];

    for (idx, param) in f.params.iter_mut().enumerate() {
        let found = prev_params
            .iter()
            .enumerate()
            .find(|(i, pp)| !matched[*i] && pp.name == param.name)
            .or_else(|| {
                if idx < prev_params.len() && !matched[idx] && prev_params[idx].ty == param.ty {
                    Some((idx, &prev_params[idx]))
                } else {
                    None
                }
            });

        if let Some((i, pp)) = found {
            matched[i] = true;
            param.id = claim_id(Some(pp.id), next_id, used);
            param.meta = merge_meta(&param.meta, Some(&pp.meta), edited_spoke);
        } else {
            param.id = claim_id(None, next_id, used);
        }
        prune_incompatible_param_meta(&mut param.meta, &param.ty, cur_enums);
    }

    let prev_body = prev.map(|p| p.body.as_slice()).unwrap_or(&[]);
    reconcile_stmts(&mut f.body, prev_body, edited_spoke, next_id, used);
}

fn stmt_kind_matches(a: &Stmt, b: &Stmt) -> bool {
    match (a, b) {
        (Stmt::Comment { .. }, Stmt::Comment { .. }) => true,
        (Stmt::Let { name: na, .. }, Stmt::Let { name: nb, .. }) => na == nb,
        (Stmt::Assign { target: ta, .. }, Stmt::Assign { target: tb, .. }) => {
            ta.root_var() == tb.root_var()
        }
        (Stmt::If { .. }, Stmt::If { .. }) => true,
        (Stmt::Match { .. }, Stmt::Match { .. }) => true,
        (Stmt::While { .. }, Stmt::While { .. }) => true,
        (Stmt::ForEach { .. }, Stmt::ForEach { .. }) => true,
        (Stmt::ForRange { .. }, Stmt::ForRange { .. }) => true,
        (Stmt::Break { .. }, Stmt::Break { .. }) => true,
        (Stmt::Continue { .. }, Stmt::Continue { .. }) => true,
        (Stmt::Return { .. }, Stmt::Return { .. }) => true,
        (
            Stmt::Assert { .. } | Stmt::AssertEq { .. },
            Stmt::Assert { .. } | Stmt::AssertEq { .. },
        ) => true,
        (Stmt::Expr { .. }, Stmt::Expr { .. }) => true,
        _ => false,
    }
}

fn reconcile_stmts(
    stmts: &mut [Stmt],
    prev_stmts: &[Stmt],
    edited_spoke: SpokeId,
    next_id: &mut NodeId,
    used: &mut HashSet<NodeId>,
) {
    let mut matched = vec![false; prev_stmts.len()];

    for stmt in stmts.iter_mut() {
        let found_idx = prev_stmts
            .iter()
            .enumerate()
            .find(|(i, ps)| !matched[*i] && stmt_kind_matches(stmt, ps))
            .map(|(i, _)| i);

        let prev_stmt = found_idx.map(|i| {
            matched[i] = true;
            &prev_stmts[i]
        });

        match stmt {
            Stmt::Comment { id, .. } => {
                let pid = match prev_stmt {
                    Some(Stmt::Comment { id: pid, .. }) => Some(*pid),
                    _ => None,
                };
                *id = claim_id(pid, next_id, used);
            }
            Stmt::Break { id } => {
                let pid = match prev_stmt {
                    Some(Stmt::Break { id: pid }) => Some(*pid),
                    _ => None,
                };
                *id = claim_id(pid, next_id, used);
            }
            Stmt::Continue { id } => {
                let pid = match prev_stmt {
                    Some(Stmt::Continue { id: pid }) => Some(*pid),
                    _ => None,
                };
                *id = claim_id(pid, next_id, used);
            }
            Stmt::Let {
                id,
                ty,
                value,
                meta,
                ..
            } => {
                if let Some(Stmt::Let {
                    id: pid,
                    ty: pty,
                    meta: pmeta,
                    ..
                }) = prev_stmt
                {
                    *id = claim_id(Some(*pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                    if ty.is_none()
                        && matches!(
                            edited_spoke,
                            SpokeId::Python
                                | SpokeId::Go
                                | SpokeId::Ruby
                                | SpokeId::Lua
                                | SpokeId::Perl
                        )
                    {
                        if pty.is_some() {
                            *ty = pty.clone();
                        }
                    } else if matches!(edited_spoke, SpokeId::C | SpokeId::Zig)
                        && pty.is_none()
                        && !matches!(value, Expr::List(items) if items.is_empty())
                    {
                        *ty = None;
                    }
                } else {
                    *id = claim_id(None, next_id, used);
                }
            }
            Stmt::Assign {
                id,
                target,
                op,
                value,
                meta,
            } => {
                if let Some(Stmt::Assign {
                    id: pid,
                    target: ptarget,
                    op: pop,
                    value: pvalue,
                    meta: pmeta,
                }) = prev_stmt
                {
                    *id = claim_id(Some(*pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                    if *pop == AssignOp::Set
                        && matches!(op, AssignOp::AddAssign | AssignOp::SubAssign)
                        && target == ptarget
                        && matches!(
                            edited_spoke,
                            SpokeId::Zig | SpokeId::C | SpokeId::Java | SpokeId::Lua
                        )
                    {
                        if let Expr::Binary {
                            op: bop,
                            left,
                            right,
                        } = pvalue
                        {
                            let op_matches = (*op == AssignOp::AddAssign && *bop == BinOp::Add)
                                || (*op == AssignOp::SubAssign && *bop == BinOp::Sub);
                            let target_expr = match target {
                                AssignTarget::Var(v) => Expr::Var(v.clone()),
                                AssignTarget::Field { base, field } => Expr::FieldAccess {
                                    base: Box::new(Expr::Var(base.clone())),
                                    field: field.clone(),
                                },
                                AssignTarget::Index { base, index } => Expr::Index {
                                    base: Box::new(Expr::Var(base.clone())),
                                    index: Box::new(index.clone()),
                                },
                            };
                            if op_matches && **left == target_expr && **right == *value {
                                *op = AssignOp::Set;
                                *value = pvalue.clone();
                            }
                        }
                    }
                } else {
                    *id = claim_id(None, next_id, used);
                }
            }
            Stmt::If {
                id,
                then_body,
                else_body,
                meta,
                ..
            } => {
                if let Some(Stmt::If {
                    id: pid,
                    then_body: pthen,
                    else_body: pelse,
                    meta: pmeta,
                    ..
                }) = prev_stmt
                {
                    *id = claim_id(Some(*pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                    reconcile_stmts(then_body, pthen, edited_spoke, next_id, used);
                    reconcile_stmts(else_body, pelse, edited_spoke, next_id, used);
                } else {
                    *id = claim_id(None, next_id, used);
                    reconcile_stmts(then_body, &[], edited_spoke, next_id, used);
                    reconcile_stmts(else_body, &[], edited_spoke, next_id, used);
                }
            }
            Stmt::Match {
                id, arms, meta, ..
            } => {
                if let Some(Stmt::Match {
                    id: pid,
                    arms: parms,
                    meta: pmeta,
                    ..
                }) = prev_stmt
                {
                    *id = claim_id(Some(*pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                    for (idx, arm) in arms.iter_mut().enumerate() {
                        let parm_body = parms.get(idx).map(|a| a.body.as_slice()).unwrap_or(&[]);
                        reconcile_stmts(&mut arm.body, parm_body, edited_spoke, next_id, used);
                    }
                } else {
                    *id = claim_id(None, next_id, used);
                    for arm in arms.iter_mut() {
                        reconcile_stmts(&mut arm.body, &[], edited_spoke, next_id, used);
                    }
                }
            }
            Stmt::While {
                id, body, meta, ..
            } => {
                if let Some(Stmt::While {
                    id: pid,
                    body: pbody,
                    meta: pmeta,
                    ..
                }) = prev_stmt
                {
                    *id = claim_id(Some(*pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                    reconcile_stmts(body, pbody, edited_spoke, next_id, used);
                } else {
                    *id = claim_id(None, next_id, used);
                    reconcile_stmts(body, &[], edited_spoke, next_id, used);
                }
            }
            Stmt::ForEach {
                id, body, meta, ..
            } => {
                if let Some(Stmt::ForEach {
                    id: pid,
                    body: pbody,
                    meta: pmeta,
                    ..
                }) = prev_stmt
                {
                    *id = claim_id(Some(*pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                    reconcile_stmts(body, pbody, edited_spoke, next_id, used);
                } else {
                    *id = claim_id(None, next_id, used);
                    reconcile_stmts(body, &[], edited_spoke, next_id, used);
                }
            }
            Stmt::ForRange {
                id, body, meta, ..
            } => {
                if let Some(Stmt::ForRange {
                    id: pid,
                    body: pbody,
                    meta: pmeta,
                    ..
                }) = prev_stmt
                {
                    *id = claim_id(Some(*pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                    reconcile_stmts(body, pbody, edited_spoke, next_id, used);
                } else {
                    *id = claim_id(None, next_id, used);
                    reconcile_stmts(body, &[], edited_spoke, next_id, used);
                }
            }
            Stmt::Return { id, meta, .. } => {
                if let Some(Stmt::Return {
                    id: pid,
                    meta: pmeta,
                    ..
                }) = prev_stmt
                {
                    *id = claim_id(Some(*pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                } else {
                    *id = claim_id(None, next_id, used);
                }
            }
            Stmt::Assert { id, meta, .. } | Stmt::AssertEq { id, meta, .. } => {
                let prev_pair = match prev_stmt {
                    Some(Stmt::Assert {
                        id: pid,
                        meta: pmeta,
                        ..
                    })
                    | Some(Stmt::AssertEq {
                        id: pid,
                        meta: pmeta,
                        ..
                    }) => Some((*pid, pmeta)),
                    _ => None,
                };
                if let Some((pid, pmeta)) = prev_pair {
                    *id = claim_id(Some(pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                } else {
                    *id = claim_id(None, next_id, used);
                }
            }
            Stmt::Expr { id, meta, .. } => {
                if let Some(Stmt::Expr {
                    id: pid,
                    meta: pmeta,
                    ..
                }) = prev_stmt
                {
                    *id = claim_id(Some(*pid), next_id, used);
                    *meta = merge_meta(meta, Some(pmeta), edited_spoke);
                } else {
                    *id = claim_id(None, next_id, used);
                }
            }
        }
    }
}

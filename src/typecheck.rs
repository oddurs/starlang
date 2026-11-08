use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, MatchPat, NodeId,
    Stmt, TestDecl, Type, UnaryOp,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticDiagnostic {
    pub node_id: NodeId,
    pub context: String,
    pub message: String,
}

impl fmt::Display for SemanticDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[Hub #{} in {}] {}",
            self.node_id, self.context, self.message
        )
    }
}

/// Central Hub Static Type & Scope Validator.
/// Validates types, symbol definitions, arities, struct fields, enum variants, and control flow
/// once in the center of the star so errors are caught across all 5 languages simultaneously.
pub fn check_module(hub: &HubModule) -> Vec<SemanticDiagnostic> {
    let mut checker = HubChecker::new(hub);
    checker.run(hub);
    checker.diags
}

struct HubChecker {
    structs: HashMap<String, HashMap<String, Type>>,
    enums: HashMap<String, HashSet<String>>,
    functions: HashMap<String, (Vec<Type>, Type)>,
    diags: Vec<SemanticDiagnostic>,
}

impl HubChecker {
    fn new(hub: &HubModule) -> Self {
        let mut structs = HashMap::new();
        let mut enums = HashMap::new();
        let mut functions = HashMap::new();
        let mut diags = Vec::new();
        let mut seen_types = HashSet::new();
        let mut seen_fns = HashSet::new();
        let mut seen_tests = HashSet::new();

        for item in &hub.items {
            match item {
                Item::Struct(s) => {
                    if !seen_types.insert(s.name.clone()) {
                        diags.push(SemanticDiagnostic {
                            node_id: s.id,
                            context: format!("struct {}", s.name),
                            message: format!("duplicate type definition '{}'", s.name),
                        });
                    }
                    let mut fmap = HashMap::new();
                    for fl in &s.fields {
                        if fmap.insert(fl.name.clone(), fl.ty.clone()).is_some() {
                            diags.push(SemanticDiagnostic {
                                node_id: fl.id,
                                context: format!("struct {}", s.name),
                                message: format!(
                                    "duplicate field '{}' in struct '{}'",
                                    fl.name, s.name
                                ),
                            });
                        }
                    }
                    structs.insert(s.name.clone(), fmap);
                }
                Item::Enum(e) => {
                    if !seen_types.insert(e.name.clone()) {
                        diags.push(SemanticDiagnostic {
                            node_id: e.id,
                            context: format!("enum {}", e.name),
                            message: format!("duplicate type definition '{}'", e.name),
                        });
                    }
                    let mut vset = HashSet::new();
                    for v in &e.variants {
                        if !vset.insert(v.clone()) {
                            diags.push(SemanticDiagnostic {
                                node_id: e.id,
                                context: format!("enum {}", e.name),
                                message: format!(
                                    "duplicate variant '{}' in enum '{}'",
                                    v, e.name
                                ),
                            });
                        }
                    }
                    enums.insert(e.name.clone(), vset);
                }
                Item::Function(f) => {
                    if !seen_fns.insert(f.name.clone()) {
                        diags.push(SemanticDiagnostic {
                            node_id: f.id,
                            context: format!("fn {}", f.name),
                            message: format!("duplicate function definition '{}'", f.name),
                        });
                    }
                    let params = f.params.iter().map(|p| p.ty.clone()).collect();
                    functions.insert(f.name.clone(), (params, f.ret_ty.clone()));
                }
                Item::Test(t) => {
                    if !seen_tests.insert(t.name.clone()) {
                        diags.push(SemanticDiagnostic {
                            node_id: t.id,
                            context: format!("test {}", t.name),
                            message: format!("duplicate test definition '{}'", t.name),
                        });
                    }
                }
            }
        }

        Self {
            structs,
            enums,
            functions,
            diags,
        }
    }

    fn types_compatible(&self, expected: &Type, actual: &Type) -> bool {
        match (expected, actual) {
            (a, b) if a == b => true,
            // TypeScript represents both Int and Float as `number`
            (Type::Float, Type::Int) => true,
            (Type::List(ea), Type::List(eb)) => self.types_compatible(ea, eb),
            _ => false,
        }
    }

    fn validate_type_exists(&mut self, ty: &Type, node_id: NodeId, ctx: &str) {
        match ty {
            Type::List(inner) => self.validate_type_exists(inner, node_id, ctx),
            Type::Named(name)
                if !self.structs.contains_key(name) && !self.enums.contains_key(name) => {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("unknown struct or enum type '{}'", name),
                    });
                }
            _ => {}
        }
    }

    fn run(&mut self, hub: &HubModule) {
        for item in &hub.items {
            match item {
                Item::Struct(s) => {
                    let ctx = format!("struct {}", s.name);
                    for fl in &s.fields {
                        self.validate_type_exists(&fl.ty, fl.id, &ctx);
                    }
                }
                Item::Enum(_) => {}
                Item::Function(f) => self.check_fn(f),
                Item::Test(t) => self.check_test(t),
            }
        }
    }

    fn check_fn(&mut self, f: &FnDecl) {
        let ctx = format!("fn {}", f.name);
        let mut env: HashMap<String, Type> = HashMap::new();
        for p in &f.params {
            self.validate_type_exists(&p.ty, p.id, &ctx);
            if env.insert(p.name.clone(), p.ty.clone()).is_some() {
                self.diags.push(SemanticDiagnostic {
                    node_id: p.id,
                    context: ctx.clone(),
                    message: format!(
                        "duplicate parameter '{}' in function '{}'",
                        p.name, f.name
                    ),
                });
            }
        }
        self.validate_type_exists(&f.ret_ty, f.id, &ctx);
        self.check_block(&f.body, &mut env, &f.ret_ty, false, &ctx);
        if f.ret_ty != Type::Void && !self.block_guarantees_return(&f.body) {
            self.diags.push(SemanticDiagnostic {
                node_id: f.id,
                context: ctx,
                message: format!(
                    "non-void function '{}' (returns {}) may exit without returning a value",
                    f.name,
                    f.ret_ty.display()
                ),
            });
        }
    }

    fn block_guarantees_return(&self, stmts: &[Stmt]) -> bool {
        stmts.iter().any(|stmt| match stmt {
            Stmt::Return { .. } => true,
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                !else_body.is_empty()
                    && self.block_guarantees_return(then_body)
                    && self.block_guarantees_return(else_body)
            }
            Stmt::Match { arms, .. } => {
                !arms.is_empty()
                    && arms.iter().all(|a| self.block_guarantees_return(&a.body))
                    && self.match_is_exhaustive(arms)
            }
            _ => false,
        })
    }

    fn match_is_exhaustive(&self, arms: &[crate::hub::MatchArm]) -> bool {
        if arms.iter().any(|a| matches!(a.pat, MatchPat::Wildcard)) {
            return true;
        }
        let mut enum_target: Option<&str> = None;
        let mut covered = HashSet::new();
        for a in arms {
            if let MatchPat::EnumVariant { enum_name, variant } = &a.pat {
                enum_target = Some(enum_name.as_str());
                covered.insert(variant.as_str());
            } else {
                return false;
            }
        }
        if let Some(en) = enum_target {
            if let Some(all_vars) = self.enums.get(en) {
                return all_vars.iter().all(|v| covered.contains(v.as_str()));
            }
        }
        false
    }

    fn check_test(&mut self, t: &TestDecl) {
        let ctx = format!("test {}", t.name);
        let mut env: HashMap<String, Type> = HashMap::new();
        self.check_block(&t.body, &mut env, &Type::Void, false, &ctx);
    }

    fn check_block(
        &mut self,
        stmts: &[Stmt],
        env: &mut HashMap<String, Type>,
        ret_ty: &Type,
        in_loop: bool,
        ctx: &str,
    ) {
        for stmt in stmts {
            match stmt {
                Stmt::Comment { .. } => {}
                Stmt::Let {
                    id,
                    name,
                    ty,
                    value,
                    ..
                } => {
                    if let Some(t) = ty {
                        self.validate_type_exists(t, *id, ctx);
                    }
                    let val_ty = self.check_expr(value, env, *id, ctx);
                    if let (Some(expected), Some(actual)) = (ty, &val_ty) {
                        if !self.types_compatible(expected, actual) {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!(
                                    "variable '{}' annotated as {}, but assigned {}",
                                    name,
                                    expected.display(),
                                    actual.display()
                                ),
                            });
                        }
                    }
                    if let Some(t) = ty.clone().or(val_ty) {
                        env.insert(name.clone(), t);
                    }
                }
                Stmt::Assign {
                    id,
                    target,
                    op,
                    value,
                    ..
                } => {
                    let tgt_ty = self.check_assign_target(target, env, *id, ctx);
                    let val_ty = self.check_expr(value, env, *id, ctx);
                    if let (Some(tt), Some(vt)) = (&tgt_ty, &val_ty) {
                        if matches!(op, AssignOp::AddAssign | AssignOp::SubAssign)
                            && !matches!(tt, Type::Int | Type::Float)
                            && !(*op == AssignOp::AddAssign && *tt == Type::Str)
                        {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!(
                                    "compound assignment requires numeric type, found {}",
                                    tt.display()
                                ),
                            });
                        } else if !self.types_compatible(tt, vt) {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!(
                                    "cannot assign {} to target of type {}",
                                    vt.display(),
                                    tt.display()
                                ),
                            });
                        }
                    }
                }
                Stmt::If {
                    id,
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    if let Some(ct) = self.check_expr(cond, env, *id, ctx) {
                        if ct != Type::Bool {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!(
                                    "'if' condition must be Bool, found {}",
                                    ct.display()
                                ),
                            });
                        }
                    }
                    let mut then_env = env.clone();
                    self.check_block(then_body, &mut then_env, ret_ty, in_loop, ctx);
                    let mut else_env = env.clone();
                    self.check_block(else_body, &mut else_env, ret_ty, in_loop, ctx);
                }
                Stmt::Match { id, expr, arms, .. } => {
                    let scrutinee_ty = self.check_expr(expr, env, *id, ctx);
                    for arm in arms {
                        if let Some(st) = &scrutinee_ty {
                            self.check_match_pat(&arm.pat, st, *id, ctx);
                        }
                        let mut arm_env = env.clone();
                        self.check_block(&arm.body, &mut arm_env, ret_ty, in_loop, ctx);
                    }
                }
                Stmt::While { id, cond, body, .. } => {
                    if let Some(ct) = self.check_expr(cond, env, *id, ctx) {
                        if ct != Type::Bool {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!(
                                    "'while' condition must be Bool, found {}",
                                    ct.display()
                                ),
                            });
                        }
                    }
                    let mut body_env = env.clone();
                    self.check_block(body, &mut body_env, ret_ty, true, ctx);
                }
                Stmt::ForEach {
                    id,
                    var,
                    iter,
                    body,
                    ..
                } => {
                    let iter_ty = self.check_expr(iter, env, *id, ctx);
                    let mut body_env = env.clone();
                    match iter_ty {
                        Some(Type::List(elem)) => {
                            body_env.insert(var.clone(), *elem);
                        }
                        Some(other) => {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!(
                                    "for-each requires List<T>, found {}",
                                    other.display()
                                ),
                            });
                        }
                        None => {}
                    }
                    self.check_block(body, &mut body_env, ret_ty, true, ctx);
                }
                Stmt::ForRange {
                    id,
                    var,
                    start,
                    end,
                    body,
                    ..
                } => {
                    if let Some(st) = self.check_expr(start, env, *id, ctx) {
                        if st != Type::Int {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!(
                                    "range start must be Int, found {}",
                                    st.display()
                                ),
                            });
                        }
                    }
                    if let Some(et) = self.check_expr(end, env, *id, ctx) {
                        if et != Type::Int {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!("range end must be Int, found {}", et.display()),
                            });
                        }
                    }
                    let mut body_env = env.clone();
                    body_env.insert(var.clone(), Type::Int);
                    self.check_block(body, &mut body_env, ret_ty, true, ctx);
                }
                Stmt::Break { id } => {
                    if !in_loop {
                        self.diags.push(SemanticDiagnostic {
                            node_id: *id,
                            context: ctx.to_string(),
                            message: "'break' used outside of a loop".to_string(),
                        });
                    }
                }
                Stmt::Continue { id } => {
                    if !in_loop {
                        self.diags.push(SemanticDiagnostic {
                            node_id: *id,
                            context: ctx.to_string(),
                            message: "'continue' used outside of a loop".to_string(),
                        });
                    }
                }
                Stmt::Return { id, value, .. } => match (ret_ty, value) {
                    (Type::Void, Some(v)) => {
                        let _ = self.check_expr(v, env, *id, ctx);
                        self.diags.push(SemanticDiagnostic {
                            node_id: *id,
                            context: ctx.to_string(),
                            message: "void function should not return a value".to_string(),
                        });
                    }
                    (expected, None) if *expected != Type::Void => {
                        self.diags.push(SemanticDiagnostic {
                            node_id: *id,
                            context: ctx.to_string(),
                            message: format!(
                                "missing return value of type {}",
                                expected.display()
                            ),
                        });
                    }
                    (expected, Some(v)) => {
                        if let Some(vt) = self.check_expr(v, env, *id, ctx) {
                            if !self.types_compatible(expected, &vt) {
                                self.diags.push(SemanticDiagnostic {
                                    node_id: *id,
                                    context: ctx.to_string(),
                                    message: format!(
                                        "expected return type {}, found {}",
                                        expected.display(),
                                        vt.display()
                                    ),
                                });
                            }
                        }
                    }
                    _ => {}
                },
                Stmt::Assert { id, cond, .. } => {
                    if let Some(ct) = self.check_expr(cond, env, *id, ctx) {
                        if ct != Type::Bool {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!(
                                    "'assert' condition must be Bool, found {}",
                                    ct.display()
                                ),
                            });
                        }
                    }
                }
                Stmt::AssertEq {
                    id, left, right, ..
                } => {
                    let lt = self.check_expr(left, env, *id, ctx);
                    let rt = self.check_expr(right, env, *id, ctx);
                    if let (Some(l), Some(r)) = (&lt, &rt) {
                        if !self.types_compatible(l, r) && !self.types_compatible(r, l) {
                            self.diags.push(SemanticDiagnostic {
                                node_id: *id,
                                context: ctx.to_string(),
                                message: format!(
                                    "'assert_eq' requires compatible types, found {} and {}",
                                    l.display(),
                                    r.display()
                                ),
                            });
                        }
                    }
                }
                Stmt::Expr { id, expr, .. } => {
                    let _ = self.check_expr(expr, env, *id, ctx);
                }
            }
        }
    }

    fn check_match_pat(
        &mut self,
        pat: &MatchPat,
        scrutinee_ty: &Type,
        node_id: NodeId,
        ctx: &str,
    ) {
        match pat {
            MatchPat::Wildcard => {}
            MatchPat::Int(_) => {
                if *scrutinee_ty != Type::Int {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!(
                            "Int match pattern used on scrutinee of type {}",
                            scrutinee_ty.display()
                        ),
                    });
                }
            }
            MatchPat::Str(_) => {
                if *scrutinee_ty != Type::Str {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!(
                            "Str match pattern used on scrutinee of type {}",
                            scrutinee_ty.display()
                        ),
                    });
                }
            }
            MatchPat::EnumVariant { enum_name, variant } => {
                if let Some(variants) = self.enums.get(enum_name) {
                    if !variants.contains(variant) {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("enum '{}' has no variant '{}'", enum_name, variant),
                        });
                    }
                } else {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("unknown enum '{}'", enum_name),
                    });
                }
                if *scrutinee_ty != Type::Named(enum_name.clone()) {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!(
                            "pattern {}::{} does not match scrutinee type {}",
                            enum_name,
                            variant,
                            scrutinee_ty.display()
                        ),
                    });
                }
            }
        }
    }

    fn check_assign_target(
        &mut self,
        target: &AssignTarget,
        env: &HashMap<String, Type>,
        node_id: NodeId,
        ctx: &str,
    ) -> Option<Type> {
        match target {
            AssignTarget::Var(v) => {
                let Some(t) = env.get(v) else {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("assignment to undeclared variable '{}'", v),
                    });
                    return None;
                };
                Some(t.clone())
            }
            AssignTarget::Field { base, field } => {
                let Some(base_ty) = env.get(base) else {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("undeclared variable '{}'", base),
                    });
                    return None;
                };
                if let Type::Named(sname) = base_ty {
                    if let Some(fields) = self.structs.get(sname) {
                        if let Some(fty) = fields.get(field) {
                            return Some(fty.clone());
                        }
                    }
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("struct '{}' has no field '{}'", sname, field),
                    });
                }
                None
            }
            AssignTarget::Index { base, index } => {
                let idx_ty = self.check_expr(index, env, node_id, ctx);
                if let Some(it) = idx_ty {
                    if it != Type::Int {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("list index must be Int, found {}", it.display()),
                        });
                    }
                }
                match env.get(base) {
                    Some(Type::List(elem)) => Some((**elem).clone()),
                    Some(other) => {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("cannot index into {}", other.display()),
                        });
                        None
                    }
                    None => {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("undeclared variable '{}'", base),
                        });
                        None
                    }
                }
            }
        }
    }

    fn check_expr(
        &mut self,
        expr: &Expr,
        env: &HashMap<String, Type>,
        node_id: NodeId,
        ctx: &str,
    ) -> Option<Type> {
        match expr {
            Expr::Int(_) => Some(Type::Int),
            Expr::Float(_) => Some(Type::Float),
            Expr::Bool(_) => Some(Type::Bool),
            Expr::Str(_) => Some(Type::Str),
            Expr::Var(name) => {
                if let Some(t) = env.get(name) {
                    Some(t.clone())
                } else {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("undeclared variable '{}'", name),
                    });
                    None
                }
            }
            Expr::EnumVariant { enum_name, variant } => {
                if let Some(variants) = self.enums.get(enum_name) {
                    if !variants.contains(variant) {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("enum '{}' has no variant '{}'", enum_name, variant),
                        });
                    }
                } else {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("unknown enum '{}'", enum_name),
                    });
                }
                Some(Type::Named(enum_name.clone()))
            }
            Expr::List(items) => {
                let mut elem_ty: Option<Type> = None;
                for it in items {
                    if let Some(t) = self.check_expr(it, env, node_id, ctx) {
                        if let Some(prev) = &elem_ty {
                            if !self.types_compatible(prev, &t) {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!(
                                        "inconsistent list element types: {} vs {}",
                                        prev.display(),
                                        t.display()
                                    ),
                                });
                            }
                        } else {
                            elem_ty = Some(t);
                        }
                    }
                }
                elem_ty.map(Type::list)
            }
            Expr::StructInit { name, fields } => {
                let Some(decl_fields) = self.structs.get(name).cloned() else {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("unknown struct '{}'", name),
                    });
                    return None;
                };
                for (fname, fval) in fields {
                    let vt = self.check_expr(fval, env, node_id, ctx);
                    if let Some(expected_ty) = decl_fields.get(fname) {
                        if let Some(vt) = vt {
                            if !self.types_compatible(expected_ty, &vt) {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!(
                                        "field '{}.{}' expects {}, found {}",
                                        name,
                                        fname,
                                        expected_ty.display(),
                                        vt.display()
                                    ),
                                });
                            }
                        }
                    } else {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("struct '{}' has no field '{}'", name, fname),
                        });
                    }
                }
                for req_name in decl_fields.keys() {
                    if !fields.iter().any(|(n, _)| n == req_name) {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("missing field '{}' in struct '{}'", req_name, name),
                        });
                    }
                }
                Some(Type::Named(name.clone()))
            }
            Expr::FieldAccess { base, field } => {
                let bty = self.check_expr(base, env, node_id, ctx)?;
                if let Type::Named(sname) = bty {
                    if let Some(fmap) = self.structs.get(&sname) {
                        if let Some(fty) = fmap.get(field) {
                            return Some(fty.clone());
                        }
                    }
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("type '{}' has no field '{}'", sname, field),
                    });
                } else {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!(
                            "cannot access field '{}' on {}",
                            field,
                            bty.display()
                        ),
                    });
                }
                None
            }
            Expr::Index { base, index } => {
                if let Some(it) = self.check_expr(index, env, node_id, ctx) {
                    if it != Type::Int {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("list index must be Int, found {}", it.display()),
                        });
                    }
                }
                match self.check_expr(base, env, node_id, ctx)? {
                    Type::List(inner) => Some(*inner),
                    other => {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("cannot index into {}", other.display()),
                        });
                        None
                    }
                }
            }
            Expr::Unary { op, expr: inner } => {
                let t = self.check_expr(inner, env, node_id, ctx)?;
                match op {
                    UnaryOp::Neg => {
                        if !matches!(t, Type::Int | Type::Float) {
                            self.diags.push(SemanticDiagnostic {
                                node_id,
                                context: ctx.to_string(),
                                message: format!("unary '-' requires Int or Float, found {}", t.display()),
                            });
                        }
                        Some(t)
                    }
                    UnaryOp::Not => {
                        if t != Type::Bool {
                            self.diags.push(SemanticDiagnostic {
                                node_id,
                                context: ctx.to_string(),
                                message: format!("logical 'not' requires Bool, found {}", t.display()),
                            });
                        }
                        Some(Type::Bool)
                    }
                }
            }
            Expr::Binary { op, left, right } => {
                let lt = self.check_expr(left, env, node_id, ctx);
                let rt = self.check_expr(right, env, node_id, ctx);
                match op {
                    BinOp::And | BinOp::Or => {
                        if let Some(l) = &lt {
                            if *l != Type::Bool {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!("boolean operator requires Bool, found {}", l.display()),
                                });
                            }
                        }
                        if let Some(r) = &rt {
                            if *r != Type::Bool {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!("boolean operator requires Bool, found {}", r.display()),
                                });
                            }
                        }
                        Some(Type::Bool)
                    }
                    BinOp::Eq | BinOp::Ne => {
                        if let (Some(l), Some(r)) = (&lt, &rt) {
                            if !self.types_compatible(l, r) && !self.types_compatible(r, l) {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!(
                                        "cannot compare {} and {} for equality",
                                        l.display(),
                                        r.display()
                                    ),
                                });
                            }
                        }
                        Some(Type::Bool)
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        if let (Some(l), Some(r)) = (&lt, &rt) {
                            if l != r || !matches!(l, Type::Int | Type::Float | Type::Str) {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!(
                                        "cannot order-compare {} and {}",
                                        l.display(),
                                        r.display()
                                    ),
                                });
                            }
                        }
                        Some(Type::Bool)
                    }
                    BinOp::Add => {
                        if let (Some(l), Some(r)) = (&lt, &rt) {
                            if l != r || !matches!(l, Type::Int | Type::Float | Type::Str) {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!(
                                        "cannot apply '+' to {} and {}",
                                        l.display(),
                                        r.display()
                                    ),
                                });
                            }
                        }
                        lt.or(rt)
                    }
                    BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::IntDiv => {
                        if let (Some(l), Some(r)) = (&lt, &rt) {
                            if l != r || !matches!(l, Type::Int | Type::Float) {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!(
                                        "arithmetic operator requires matching numeric types, found {} and {}",
                                        l.display(),
                                        r.display()
                                    ),
                                });
                            }
                        }
                        if *op == BinOp::Div {
                            Some(Type::Float)
                        } else if *op == BinOp::IntDiv {
                            Some(Type::Int)
                        } else {
                            lt.or(rt)
                        }
                    }
                    BinOp::Mod => {
                        if let (Some(l), Some(r)) = (&lt, &rt) {
                            if *l != Type::Int || *r != Type::Int {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!(
                                        "modulo operator '%' requires Int operands, found {} and {}",
                                        l.display(),
                                        r.display()
                                    ),
                                });
                            }
                        }
                        Some(Type::Int)
                    }
                }
            }
            Expr::Call { func, args } => {
                let Some((param_tys, ret_ty)) = self.functions.get(func).cloned() else {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!("call to undefined function '{}'", func),
                    });
                    for a in args {
                        let _ = self.check_expr(a, env, node_id, ctx);
                    }
                    return None;
                };
                if args.len() != param_tys.len() {
                    self.diags.push(SemanticDiagnostic {
                        node_id,
                        context: ctx.to_string(),
                        message: format!(
                            "function '{}' expects {} argument(s), got {}",
                            func,
                            param_tys.len(),
                            args.len()
                        ),
                    });
                }
                for (i, a) in args.iter().enumerate() {
                    if let (Some(at), Some(pt)) =
                        (self.check_expr(a, env, node_id, ctx), param_tys.get(i))
                    {
                        if !self.types_compatible(pt, &at) {
                            self.diags.push(SemanticDiagnostic {
                                node_id,
                                context: ctx.to_string(),
                                message: format!(
                                    "argument {} to '{}' expects {}, found {}",
                                    i + 1,
                                    func,
                                    pt.display(),
                                    at.display()
                                ),
                            });
                        }
                    }
                }
                Some(ret_ty)
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e) => {
                    if let Some(t) = self.check_expr(e, env, node_id, ctx) {
                        if !matches!(t, Type::List(_) | Type::Str) {
                            self.diags.push(SemanticDiagnostic {
                                node_id,
                                context: ctx.to_string(),
                                message: format!("len() requires List or Str, found {}", t.display()),
                            });
                        }
                    }
                    Some(Type::Int)
                }
                Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                    let at = self.check_expr(a, env, node_id, ctx);
                    let bt = self.check_expr(b, env, node_id, ctx);
                    if let (Some(la), Some(lb)) = (&at, &bt) {
                        if la != lb || !matches!(la, Type::Int | Type::Float) {
                            self.diags.push(SemanticDiagnostic {
                                node_id,
                                context: ctx.to_string(),
                                message: format!(
                                    "min/max requires matching numeric types, found {} and {}",
                                    la.display(),
                                    lb.display()
                                ),
                            });
                        }
                    }
                    at.or(bt)
                }
                Intrinsic::Abs(a) => {
                    let at = self.check_expr(a, env, node_id, ctx);
                    if let Some(la) = &at {
                        if !matches!(la, Type::Int | Type::Float) {
                            self.diags.push(SemanticDiagnostic {
                                node_id,
                                context: ctx.to_string(),
                                message: format!("abs() requires number, found {}", la.display()),
                            });
                        }
                    }
                    at
                }
                Intrinsic::Push { list, value } => {
                    let lt = self.check_expr(list, env, node_id, ctx);
                    let vt = self.check_expr(value, env, node_id, ctx);
                    if let Some(Type::List(elem)) = lt {
                        if let Some(v) = vt {
                            if !self.types_compatible(&elem, &v) {
                                self.diags.push(SemanticDiagnostic {
                                    node_id,
                                    context: ctx.to_string(),
                                    message: format!(
                                        "cannot push {} onto List<{}>",
                                        v.display(),
                                        elem.display()
                                    ),
                                });
                            }
                        }
                    } else if let Some(other) = lt {
                        self.diags.push(SemanticDiagnostic {
                            node_id,
                            context: ctx.to_string(),
                            message: format!("push requires List<T>, found {}", other.display()),
                        });
                    }
                    Some(Type::Void)
                }
                Intrinsic::Print(args) => {
                    for a in args {
                        let _ = self.check_expr(a, env, node_id, ctx);
                    }
                    Some(Type::Void)
                }
                Intrinsic::Contains { haystack, needle } => {
                    let ht = self.check_expr(haystack, env, node_id, ctx);
                    let nt = self.check_expr(needle, env, node_id, ctx);
                    match (ht, nt) {
                        (Some(Type::Str), Some(Type::Str)) => {}
                        (Some(Type::List(elem)), Some(n)) if self.types_compatible(&elem, &n) => {}
                        (Some(h), Some(n)) => {
                            self.diags.push(SemanticDiagnostic {
                                node_id,
                                context: ctx.to_string(),
                                message: format!(
                                    "contains() incompatible for {} and {}",
                                    h.display(),
                                    n.display()
                                ),
                            });
                        }
                        _ => {}
                    }
                    Some(Type::Bool)
                }
                Intrinsic::Upper(e) | Intrinsic::Lower(e) => {
                    if let Some(t) = self.check_expr(e, env, node_id, ctx) {
                        if t != Type::Str {
                            self.diags.push(SemanticDiagnostic {
                                node_id,
                                context: ctx.to_string(),
                                message: format!("case conversion requires Str, found {}", t.display()),
                            });
                        }
                    }
                    Some(Type::Str)
                }
                Intrinsic::ToStr(e) => {
                    let _ = self.check_expr(e, env, node_id, ctx);
                    Some(Type::Str)
                }
            },
        }
    }
}

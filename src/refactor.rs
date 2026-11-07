use std::collections::{BTreeSet, HashMap, HashSet};

use crate::hub::{
    infer_expr_type, normalize_module, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic,
    Item, MatchPat, Stmt, TestDecl, Type, UnaryOp,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolEntry {
    /// Canonical target selector (e.g. `"fn:clamp_scores"`, `"field:Summary.average"`, `"var:main::raw"`).
    pub spec: String,
    /// Human-readable label shown in UI dropdowns & CLI listings.
    pub label: String,
    pub current_name: String,
}

/// Enumerate every renameable symbol in `hub` in deterministic declaration order.
pub fn list_symbols(hub: &HubModule) -> Vec<SymbolEntry> {
    let mut out = Vec::new();
    for item in &hub.items {
        match item {
            Item::Struct(s) => {
                out.push(SymbolEntry {
                    spec: format!("struct:{}", s.name),
                    label: format!("struct {}", s.name),
                    current_name: s.name.clone(),
                });
                for f in &s.fields {
                    out.push(SymbolEntry {
                        spec: format!("field:{}.{}", s.name, f.name),
                        label: format!("field {}.{}", s.name, f.name),
                        current_name: f.name.clone(),
                    });
                }
            }
            Item::Enum(e) => {
                out.push(SymbolEntry {
                    spec: format!("enum:{}", e.name),
                    label: format!("enum {}", e.name),
                    current_name: e.name.clone(),
                });
                for v in &e.variants {
                    out.push(SymbolEntry {
                        spec: format!("variant:{}::{}", e.name, v),
                        label: format!("variant {}::{}", e.name, v),
                        current_name: v.clone(),
                    });
                }
            }
            Item::Function(f) => {
                if f.name != "main" {
                    out.push(SymbolEntry {
                        spec: format!("fn:{}", f.name),
                        label: format!("fn {}()", f.name),
                        current_name: f.name.clone(),
                    });
                }
                let mut locals = BTreeSet::new();
                for p in &f.params {
                    locals.insert(p.name.clone());
                }
                collect_declared_locals(&f.body, &mut locals);
                for v in locals {
                    out.push(SymbolEntry {
                        spec: format!("var:{}::{}", f.name, v),
                        label: format!("var {}::{}", f.name, v),
                        current_name: v,
                    });
                }
            }
            Item::Test(t) => {
                out.push(SymbolEntry {
                    spec: format!("test:{}", t.name),
                    label: format!("test {}", t.name),
                    current_name: t.name.clone(),
                });
            }
        }
    }
    out
}

fn collect_declared_locals(stmts: &[Stmt], out: &mut BTreeSet<String>) {
    for s in stmts {
        match s {
            Stmt::Let { name, .. } => {
                out.insert(name.clone());
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_declared_locals(then_body, out);
                collect_declared_locals(else_body, out);
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    collect_declared_locals(&a.body, out);
                }
            }
            Stmt::While { body, .. } => collect_declared_locals(body, out),
            Stmt::ForEach { var, body, .. } | Stmt::ForRange { var, body, .. } => {
                out.insert(var.clone());
                collect_declared_locals(body, out);
            }
            _ => {}
        }
    }
}

#[derive(Debug, Clone)]
enum RenameTarget {
    Function(String),
    Test(String),
    TypeName(String),
    Field { struct_name: String, field: String },
    Variant { enum_name: String, variant: String },
    LocalVar { fn_name: String, var: String },
}

const RESERVED_WORDS: &[&str] = &[
    "fn", "func", "def", "function", "struct", "class", "enum", "type", "interface", "export",
    "import", "package", "from", "as", "const", "let", "var", "mut", "auto", "pub", "return",
    "if", "else", "elif", "elsif", "unless", "match", "switch", "case", "when", "default", "for",
    "while", "in", "of", "range", "break", "continue", "next", "end", "module", "begin", "rescue",
    "ensure", "nil", "true", "false", "None", "void", "int", "int64", "int64_t", "float",
    "float64", "double", "bool", "boolean", "str", "string", "number", "Vec", "String", "main",
];

fn validate_identifier(name: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err("new identifier cannot be empty".to_string());
    }
    let mut chars = name.chars();
    let first = chars.next().unwrap();
    if !(first.is_ascii_alphabetic() || first == '_') {
        return Err(format!(
            "'{}' must start with an ASCII letter or '_'",
            name
        ));
    }
    if !chars.all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return Err(format!(
            "'{}' must contain only ASCII letters, digits, or '_'",
            name
        ));
    }
    if RESERVED_WORDS.contains(&name) {
        return Err(format!(
            "'{}' is a reserved keyword in one or more spoke languages",
            name
        ));
    }
    Ok(())
}

fn resolve_target(hub: &HubModule, spec: &str) -> Result<RenameTarget, String> {
    if let Some(rest) = spec.strip_prefix("fn:") {
        if hub.find_fn(rest).is_none() {
            return Err(format!("unknown function '{}'", rest));
        }
        if rest == "main" {
            return Err("cannot rename entrypoint 'main'".to_string());
        }
        return Ok(RenameTarget::Function(rest.to_string()));
    }
    if let Some(rest) = spec.strip_prefix("test:") {
        if hub.find_test(rest).is_none() {
            return Err(format!("unknown test '{}'", rest));
        }
        return Ok(RenameTarget::Test(rest.to_string()));
    }
    if let Some(rest) = spec.strip_prefix("struct:") {
        if hub.find_struct(rest).is_none() {
            return Err(format!("unknown struct '{}'", rest));
        }
        return Ok(RenameTarget::TypeName(rest.to_string()));
    }
    if let Some(rest) = spec.strip_prefix("enum:") {
        if hub.find_enum(rest).is_none() {
            return Err(format!("unknown enum '{}'", rest));
        }
        return Ok(RenameTarget::TypeName(rest.to_string()));
    }
    if let Some(rest) = spec.strip_prefix("field:") {
        let Some((sname, fname)) = rest.split_once('.') else {
            return Err("field selector must look like 'field:Struct.field'".to_string());
        };
        let Some(s) = hub.find_struct(sname) else {
            return Err(format!("unknown struct '{}'", sname));
        };
        if !s.fields.iter().any(|f| f.name == fname) {
            return Err(format!("struct '{}' has no field '{}'", sname, fname));
        }
        return Ok(RenameTarget::Field {
            struct_name: sname.to_string(),
            field: fname.to_string(),
        });
    }
    if let Some(rest) = spec.strip_prefix("variant:") {
        let Some((ename, vname)) = rest.split_once("::") else {
            return Err("variant selector must look like 'variant:Enum::Variant'".to_string());
        };
        let Some(e) = hub.find_enum(ename) else {
            return Err(format!("unknown enum '{}'", ename));
        };
        if !e.variants.iter().any(|v| v == vname) {
            return Err(format!("enum '{}' has no variant '{}'", ename, vname));
        }
        return Ok(RenameTarget::Variant {
            enum_name: ename.to_string(),
            variant: vname.to_string(),
        });
    }
    if let Some(rest) = spec.strip_prefix("var:") {
        let Some((fn_name, var)) = rest.split_once("::") else {
            return Err("variable selector must look like 'var:fn_name::var'".to_string());
        };
        if hub.find_fn(fn_name).is_none() {
            return Err(format!("unknown function '{}'", fn_name));
        }
        return Ok(RenameTarget::LocalVar {
            fn_name: fn_name.to_string(),
            var: var.to_string(),
        });
    }

    // Convenience bare-syntax resolution for CLI: `Struct.field`, `Enum::Variant` or `fn::var`, or top-level name
    if let Some((sname, fname)) = spec.split_once('.') {
        return resolve_target(hub, &format!("field:{}.{}", sname, fname));
    }
    if let Some((lhs, rhs)) = spec.split_once("::") {
        if hub.find_enum(lhs).is_some() {
            return resolve_target(hub, &format!("variant:{}::{}", lhs, rhs));
        }
        return resolve_target(hub, &format!("var:{}::{}", lhs, rhs));
    }
    if hub.find_fn(spec).is_some() {
        return resolve_target(hub, &format!("fn:{}", spec));
    }
    if hub.find_struct(spec).is_some() {
        return resolve_target(hub, &format!("struct:{}", spec));
    }
    if hub.find_enum(spec).is_some() {
        return resolve_target(hub, &format!("enum:{}", spec));
    }
    Err(format!("symbol '{}' not found in Hub module", spec))
}

/// Scope-aware, type-directed cross-language symbol rename on the Central Hub.
/// Updates declarations, types, struct literals/fields, enum variants, pattern arms, and call sites,
/// while preserving all NodeIds and spoke-specific metadata (`rust.pass`, `cpp.pass`, etc.).
pub fn rename_symbol(
    hub: &HubModule,
    target_spec: &str,
    new_name: &str,
) -> Result<(HubModule, usize), String> {
    let new_name = new_name.trim();
    validate_identifier(new_name)?;
    let target = resolve_target(hub, target_spec.trim())?;

    // Check collisions before mutating
    match &target {
        RenameTarget::Function(old) => {
            if old == new_name {
                return Ok((hub.clone(), 0));
            }
            if hub.find_fn(new_name).is_some() {
                return Err(format!("function '{}' already exists", new_name));
            }
        }
        RenameTarget::Test(old) => {
            let canon = new_name.strip_prefix("test_").unwrap_or(new_name);
            if old == canon {
                return Ok((hub.clone(), 0));
            }
            if hub.find_test(canon).is_some() {
                return Err(format!("test '{}' already exists", canon));
            }
        }
        RenameTarget::TypeName(old) => {
            if old == new_name {
                return Ok((hub.clone(), 0));
            }
            if hub.find_struct(new_name).is_some() || hub.find_enum(new_name).is_some() {
                return Err(format!("type '{}' already exists", new_name));
            }
        }
        RenameTarget::Field { struct_name, field } => {
            if field == new_name {
                return Ok((hub.clone(), 0));
            }
            if let Some(s) = hub.find_struct(struct_name) {
                if s.fields.iter().any(|f| f.name == new_name) {
                    return Err(format!(
                        "struct '{}' already has a field '{}'",
                        struct_name, new_name
                    ));
                }
            }
        }
        RenameTarget::Variant { enum_name, variant } => {
            if variant == new_name {
                return Ok((hub.clone(), 0));
            }
            if let Some(e) = hub.find_enum(enum_name) {
                if e.variants.iter().any(|v| v == new_name) {
                    return Err(format!(
                        "enum '{}' already has a variant '{}'",
                        enum_name, new_name
                    ));
                }
            }
        }
        RenameTarget::LocalVar { var, .. } => {
            if var == new_name {
                return Ok((hub.clone(), 0));
            }
        }
    }

    // Build type tables on original Hub so field-access type inference is exact
    let mut fn_ret_types: HashMap<String, Type> = HashMap::new();
    let mut struct_fields: HashMap<String, HashMap<String, Type>> = HashMap::new();
    let mut enum_names: HashSet<String> = HashSet::new();
    for item in &hub.items {
        match item {
            Item::Function(f) => {
                fn_ret_types.insert(f.name.clone(), f.ret_ty.clone());
            }
            Item::Struct(s) => {
                let mut m = HashMap::new();
                for fl in &s.fields {
                    m.insert(fl.name.clone(), fl.ty.clone());
                }
                struct_fields.insert(s.name.clone(), m);
            }
            Item::Enum(e) => {
                enum_names.insert(e.name.clone());
            }
            Item::Test(_) => {}
        }
    }

    let mut updated = hub.clone();
    let mut count = 0usize;

    for item in &mut updated.items {
        match item {
            Item::Struct(s) => {
                if let RenameTarget::TypeName(old) = &target {
                    if s.name == *old {
                        s.name = new_name.to_string();
                        count += 1;
                    }
                    for f in &mut s.fields {
                        count += rename_in_type(&mut f.ty, old, new_name);
                    }
                } else if let RenameTarget::Field { struct_name, field } = &target {
                    if s.name == *struct_name {
                        for f in &mut s.fields {
                            if f.name == *field {
                                f.name = new_name.to_string();
                                count += 1;
                            }
                        }
                    }
                }
            }
            Item::Enum(e) => {
                if let RenameTarget::TypeName(old) = &target {
                    if e.name == *old {
                        e.name = new_name.to_string();
                        count += 1;
                    }
                } else if let RenameTarget::Variant { enum_name, variant } = &target {
                    if e.name == *enum_name {
                        for v in &mut e.variants {
                            if v == variant {
                                *v = new_name.to_string();
                                count += 1;
                            }
                        }
                    }
                }
            }
            Item::Function(f) => {
                let orig_fn_name = f.name.clone();
                // Seed local type env using pre-rename types so field lookups resolve cleanly
                let mut env: HashMap<String, Type> = HashMap::new();
                for p in &f.params {
                    env.insert(p.name.clone(), p.ty.clone());
                }

                match &target {
                    RenameTarget::Function(old) => {
                        if f.name == *old {
                            f.name = new_name.to_string();
                            count += 1;
                        }
                    }
                    RenameTarget::TypeName(old) => {
                        for p in &mut f.params {
                            count += rename_in_type(&mut p.ty, old, new_name);
                        }
                        count += rename_in_type(&mut f.ret_ty, old, new_name);
                    }
                    RenameTarget::LocalVar { fn_name, var } if *fn_name == orig_fn_name => {
                        for p in &mut f.params {
                            if p.name == *var {
                                p.name = new_name.to_string();
                                count += 1;
                            }
                        }
                    }
                    _ => {}
                }

                let mut ctx = RenameWalkCtx {
                    target: &target,
                    new_name,
                    in_target_fn: matches!(
                        &target,
                        RenameTarget::LocalVar { fn_name, .. } if *fn_name == orig_fn_name
                    ),
                    fn_ret_types: &fn_ret_types,
                    struct_fields: &struct_fields,
                    enum_names: &enum_names,
                    count: &mut count,
                };
                ctx.walk_block(&mut f.body, &mut env);
            }
            Item::Test(t) => {
                if let RenameTarget::Test(old) = &target {
                    if t.name == *old {
                        t.name = new_name
                            .strip_prefix("test_")
                            .unwrap_or(new_name)
                            .to_string();
                        count += 1;
                    }
                }
                let mut env: HashMap<String, Type> = HashMap::new();
                let mut ctx = RenameWalkCtx {
                    target: &target,
                    new_name,
                    in_target_fn: false,
                    fn_ret_types: &fn_ret_types,
                    struct_fields: &struct_fields,
                    enum_names: &enum_names,
                    count: &mut count,
                };
                ctx.walk_block(&mut t.body, &mut env);
            }
        }
    }

    Ok((updated, count))
}

fn rename_in_type(ty: &mut Type, old_type: &str, new_type: &str) -> usize {
    match ty {
        Type::Named(n) if n == old_type => {
            *n = new_type.to_string();
            1
        }
        Type::List(inner) => rename_in_type(inner, old_type, new_type),
        _ => 0,
    }
}

struct RenameWalkCtx<'a> {
    target: &'a RenameTarget,
    new_name: &'a str,
    in_target_fn: bool,
    fn_ret_types: &'a HashMap<String, Type>,
    struct_fields: &'a HashMap<String, HashMap<String, Type>>,
    enum_names: &'a HashSet<String>,
    count: &'a mut usize,
}

impl<'a> RenameWalkCtx<'a> {
    fn walk_block(&mut self, stmts: &mut [Stmt], env: &mut HashMap<String, Type>) {
        for stmt in stmts {
            match stmt {
                Stmt::Comment { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {}
                Stmt::Let {
                    name, ty, value, ..
                } => {
                    self.walk_expr(value, env);
                    let inferred = ty.clone().or_else(|| {
                        infer_expr_type(
                            value,
                            env,
                            self.fn_ret_types,
                            self.struct_fields,
                            self.enum_names,
                        )
                    });
                    if let Some(t) = inferred {
                        env.insert(name.clone(), t);
                    }
                    if let Some(t) = ty {
                        if let RenameTarget::TypeName(old) = self.target {
                            *self.count += rename_in_type(t, old, self.new_name);
                        }
                    }
                    if self.in_target_fn {
                        if let RenameTarget::LocalVar { var, .. } = self.target {
                            if name == var {
                                *name = self.new_name.to_string();
                                *self.count += 1;
                            }
                        }
                    }
                }
                Stmt::Assign { target, value, .. } => {
                    self.walk_expr(value, env);
                    match target {
                        AssignTarget::Var(v) => {
                            if self.in_target_fn {
                                if let RenameTarget::LocalVar { var, .. } = self.target {
                                    if v == var {
                                        *v = self.new_name.to_string();
                                        *self.count += 1;
                                    }
                                }
                            }
                        }
                        AssignTarget::Field { base, field } => {
                            if let RenameTarget::Field {
                                struct_name,
                                field: target_field,
                            } = self.target
                            {
                                if field == target_field
                                    && env.get(base) == Some(&Type::Named(struct_name.clone()))
                                {
                                    *field = self.new_name.to_string();
                                    *self.count += 1;
                                }
                            }
                            if self.in_target_fn {
                                if let RenameTarget::LocalVar { var, .. } = self.target {
                                    if base == var {
                                        *base = self.new_name.to_string();
                                        *self.count += 1;
                                    }
                                }
                            }
                        }
                        AssignTarget::Index { base, index } => {
                            self.walk_expr(index, env);
                            if self.in_target_fn {
                                if let RenameTarget::LocalVar { var, .. } = self.target {
                                    if base == var {
                                        *base = self.new_name.to_string();
                                        *self.count += 1;
                                    }
                                }
                            }
                        }
                    }
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    self.walk_expr(cond, env);
                    let mut then_env = env.clone();
                    self.walk_block(then_body, &mut then_env);
                    let mut else_env = env.clone();
                    self.walk_block(else_body, &mut else_env);
                }
                Stmt::Match { expr, arms, .. } => {
                    self.walk_expr(expr, env);
                    for arm in arms {
                        match &mut arm.pat {
                            MatchPat::EnumVariant { enum_name, variant } => match self.target {
                                RenameTarget::TypeName(old) if enum_name == old => {
                                    *enum_name = self.new_name.to_string();
                                    *self.count += 1;
                                }
                                RenameTarget::Variant {
                                    enum_name: te,
                                    variant: tv,
                                } if enum_name == te && variant == tv => {
                                    *variant = self.new_name.to_string();
                                    *self.count += 1;
                                }
                                _ => {}
                            },
                            _ => {}
                        }
                        let mut arm_env = env.clone();
                        self.walk_block(&mut arm.body, &mut arm_env);
                    }
                }
                Stmt::While { cond, body, .. } => {
                    self.walk_expr(cond, env);
                    let mut inner_env = env.clone();
                    self.walk_block(body, &mut inner_env);
                }
                Stmt::ForEach {
                    var, iter, body, ..
                } => {
                    self.walk_expr(iter, env);
                    let mut inner_env = env.clone();
                    if let Some(Type::List(elem)) = infer_expr_type(
                        iter,
                        env,
                        self.fn_ret_types,
                        self.struct_fields,
                        self.enum_names,
                    ) {
                        inner_env.insert(var.clone(), *elem);
                    }
                    if self.in_target_fn {
                        if let RenameTarget::LocalVar { var: tvar, .. } = self.target {
                            if var == tvar {
                                *var = self.new_name.to_string();
                                *self.count += 1;
                            }
                        }
                    }
                    self.walk_block(body, &mut inner_env);
                }
                Stmt::ForRange {
                    var,
                    start,
                    end,
                    body,
                    ..
                } => {
                    self.walk_expr(start, env);
                    self.walk_expr(end, env);
                    let mut inner_env = env.clone();
                    inner_env.insert(var.clone(), Type::Int);
                    if self.in_target_fn {
                        if let RenameTarget::LocalVar { var: tvar, .. } = self.target {
                            if var == tvar {
                                *var = self.new_name.to_string();
                                *self.count += 1;
                            }
                        }
                    }
                    self.walk_block(body, &mut inner_env);
                }
                Stmt::Return { value: Some(e), .. }
                | Stmt::Assert { cond: e, .. }
                | Stmt::Expr { expr: e, .. } => {
                    self.walk_expr(e, env);
                }
                Stmt::AssertEq { left, right, .. } => {
                    self.walk_expr(left, env);
                    self.walk_expr(right, env);
                }
                Stmt::Return { value: None, .. } => {}
            }
        }
    }

    fn walk_expr(&mut self, expr: &mut Expr, env: &HashMap<String, Type>) {
        match expr {
            Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Str(_) => {}
            Expr::Var(v) => {
                if self.in_target_fn {
                    if let RenameTarget::LocalVar { var, .. } = self.target {
                        if v == var {
                            *v = self.new_name.to_string();
                            *self.count += 1;
                        }
                    }
                }
            }
            Expr::EnumVariant { enum_name, variant } => match self.target {
                RenameTarget::TypeName(old) if enum_name == old => {
                    *enum_name = self.new_name.to_string();
                    *self.count += 1;
                }
                RenameTarget::Variant {
                    enum_name: te,
                    variant: tv,
                } if enum_name == te && variant == tv => {
                    *variant = self.new_name.to_string();
                    *self.count += 1;
                }
                _ => {}
            },
            Expr::List(items) => {
                for it in items {
                    self.walk_expr(it, env);
                }
            }
            Expr::StructInit { name, fields } => {
                let orig_struct_name = name.clone();
                if let RenameTarget::TypeName(old) = self.target {
                    if name == old {
                        *name = self.new_name.to_string();
                        *self.count += 1;
                    }
                }
                for (fname, fexpr) in fields {
                    self.walk_expr(fexpr, env);
                    if let RenameTarget::Field {
                        struct_name,
                        field: target_field,
                    } = self.target
                    {
                        if orig_struct_name == *struct_name && fname == target_field {
                            *fname = self.new_name.to_string();
                            *self.count += 1;
                        }
                    }
                }
            }
            Expr::FieldAccess { base, field } => {
                // Infer base type BEFORE walking base (in case base is a local variable being renamed)
                let base_ty = infer_expr_type(
                    base,
                    env,
                    self.fn_ret_types,
                    self.struct_fields,
                    self.enum_names,
                );
                self.walk_expr(base, env);
                if let RenameTarget::Field {
                    struct_name,
                    field: target_field,
                } = self.target
                {
                    if field == target_field && base_ty == Some(Type::Named(struct_name.clone())) {
                        *field = self.new_name.to_string();
                        *self.count += 1;
                    }
                }
            }
            Expr::Index { base, index } => {
                self.walk_expr(base, env);
                self.walk_expr(index, env);
            }
            Expr::Unary { expr: inner, .. } => self.walk_expr(inner, env),
            Expr::Binary { left, right, .. } => {
                self.walk_expr(left, env);
                self.walk_expr(right, env);
            }
            Expr::Call { func, args } => {
                if let RenameTarget::Function(old) = self.target {
                    if func == old {
                        *func = self.new_name.to_string();
                        *self.count += 1;
                    }
                }
                for a in args {
                    self.walk_expr(a, env);
                }
            }
            Expr::Intrinsic(intr) => match intr.as_mut() {
                Intrinsic::Len(e)
                | Intrinsic::Abs(e)
                | Intrinsic::Upper(e)
                | Intrinsic::Lower(e)
                | Intrinsic::ToStr(e) => self.walk_expr(e, env),
                Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                    self.walk_expr(a, env);
                    self.walk_expr(b, env);
                }
                Intrinsic::Push { list, value } => {
                    self.walk_expr(list, env);
                    self.walk_expr(value, env);
                }
                Intrinsic::Print(args) => {
                    for a in args {
                        self.walk_expr(a, env);
                    }
                }
                Intrinsic::Contains { haystack, needle } => {
                    self.walk_expr(haystack, env);
                    self.walk_expr(needle, env);
                }
            },
        }
    }
}

// ============================================================================
// Central Hub Semantic Optimizer (Constant Folding + Dead-Branch Pruning)
// ============================================================================

/// Optimize a `HubModule` once in the center so all 6 spoke views simplify simultaneously.
/// Returns `(optimized_module, rewrite_count)`.
pub fn optimize_module(hub: &HubModule) -> (HubModule, usize) {
    let mut out = hub.clone();
    let mut rewrites = 0usize;

    for item in &mut out.items {
        match item {
            Item::Function(FnDecl { body, .. }) | Item::Test(TestDecl { body, .. }) => {
                *body = opt_block(std::mem::take(body), &mut rewrites);
            }
            _ => {}
        }
    }

    if rewrites > 0 {
        normalize_module(&mut out);
    }
    (out, rewrites)
}

fn opt_block(stmts: Vec<Stmt>, rewrites: &mut usize) -> Vec<Stmt> {
    let mut result = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        match stmt {
            Stmt::Let {
                id,
                name,
                mutable,
                ty,
                mut value,
                meta,
            } => {
                opt_expr(&mut value, rewrites);
                result.push(Stmt::Let {
                    id,
                    name,
                    mutable,
                    ty,
                    value,
                    meta,
                });
            }
            Stmt::Assign {
                id,
                mut target,
                op,
                mut value,
                meta,
            } => {
                if let AssignTarget::Index { index, .. } = &mut target {
                    opt_expr(index, rewrites);
                }
                opt_expr(&mut value, rewrites);
                result.push(Stmt::Assign {
                    id,
                    target,
                    op,
                    value,
                    meta,
                });
            }
            Stmt::If {
                id,
                mut cond,
                then_body,
                else_body,
                meta,
            } => {
                opt_expr(&mut cond, rewrites);
                let then_opt = opt_block(then_body, rewrites);
                let else_opt = opt_block(else_body, rewrites);
                if let Expr::Bool(b) = cond {
                    *rewrites += 1;
                    if b {
                        result.extend(then_opt);
                    } else {
                        result.extend(else_opt);
                    }
                } else {
                    result.push(Stmt::If {
                        id,
                        cond,
                        then_body: then_opt,
                        else_body: else_opt,
                        meta,
                    });
                }
            }
            Stmt::Match {
                id,
                mut expr,
                mut arms,
                meta,
            } => {
                opt_expr(&mut expr, rewrites);
                for arm in &mut arms {
                    arm.body = opt_block(std::mem::take(&mut arm.body), rewrites);
                }
                result.push(Stmt::Match {
                    id,
                    expr,
                    arms,
                    meta,
                });
            }
            Stmt::While {
                id,
                mut cond,
                body,
                meta,
            } => {
                opt_expr(&mut cond, rewrites);
                if cond == Expr::Bool(false) {
                    *rewrites += 1;
                } else {
                    let body_opt = opt_block(body, rewrites);
                    result.push(Stmt::While {
                        id,
                        cond,
                        body: body_opt,
                        meta,
                    });
                }
            }
            Stmt::ForEach {
                id,
                var,
                mut iter,
                body,
                meta,
            } => {
                opt_expr(&mut iter, rewrites);
                let body_opt = opt_block(body, rewrites);
                result.push(Stmt::ForEach {
                    id,
                    var,
                    iter,
                    body: body_opt,
                    meta,
                });
            }
            Stmt::ForRange {
                id,
                var,
                mut start,
                mut end,
                body,
                meta,
            } => {
                opt_expr(&mut start, rewrites);
                opt_expr(&mut end, rewrites);
                let body_opt = opt_block(body, rewrites);
                result.push(Stmt::ForRange {
                    id,
                    var,
                    start,
                    end,
                    body: body_opt,
                    meta,
                });
            }
            Stmt::Return {
                id,
                value: Some(mut e),
                meta,
            } => {
                opt_expr(&mut e, rewrites);
                result.push(Stmt::Return {
                    id,
                    value: Some(e),
                    meta,
                });
            }
            Stmt::Assert { id, mut cond, meta } => {
                opt_expr(&mut cond, rewrites);
                result.push(Stmt::Assert { id, cond, meta });
            }
            Stmt::AssertEq {
                id,
                mut left,
                mut right,
                meta,
            } => {
                opt_expr(&mut left, rewrites);
                opt_expr(&mut right, rewrites);
                result.push(Stmt::AssertEq {
                    id,
                    left,
                    right,
                    meta,
                });
            }
            Stmt::Expr {
                id,
                mut expr,
                meta,
            } => {
                opt_expr(&mut expr, rewrites);
                result.push(Stmt::Expr { id, expr, meta });
            }
            other => result.push(other),
        }
    }
    result
}

fn const_int(e: &Expr) -> Option<i64> {
    match e {
        Expr::Int(v) => Some(*v),
        Expr::Unary {
            op: UnaryOp::Neg,
            expr: inner,
        } => {
            if let Expr::Int(v) = inner.as_ref() {
                v.checked_neg()
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Build canonical Hub integer expression (`Unary(Neg, Int(v))` for negatives so `GetPut` holds).
fn canonical_int_expr(v: i64) -> Expr {
    if v < 0 {
        Expr::Unary {
            op: UnaryOp::Neg,
            expr: Box::new(Expr::Int(v.saturating_abs())),
        }
    } else {
        Expr::Int(v)
    }
}

fn is_pure_expr(e: &Expr) -> bool {
    match e {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Bool(_)
        | Expr::Str(_)
        | Expr::Var(_)
        | Expr::EnumVariant { .. } => true,
        Expr::List(items) => items.iter().all(is_pure_expr),
        Expr::StructInit { fields, .. } => fields.iter().all(|(_, v)| is_pure_expr(v)),
        Expr::FieldAccess { base, .. } => is_pure_expr(base),
        Expr::Unary { expr: inner, .. } => is_pure_expr(inner),
        Expr::Binary { left, right, .. } => is_pure_expr(left) && is_pure_expr(right),
        _ => false,
    }
}

fn opt_expr(expr: &mut Expr, rewrites: &mut usize) {
    match expr {
        Expr::List(items) => {
            for it in items {
                opt_expr(it, rewrites);
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, v) in fields {
                opt_expr(v, rewrites);
            }
        }
        Expr::FieldAccess { base, .. } => opt_expr(base, rewrites),
        Expr::Index { base, index } => {
            opt_expr(base, rewrites);
            opt_expr(index, rewrites);
        }
        Expr::Call { args, .. } => {
            for a in args {
                opt_expr(a, rewrites);
            }
        }
        Expr::Unary { op, expr: inner } => {
            opt_expr(inner, rewrites);
            match (*op, inner.as_ref()) {
                (UnaryOp::Not, Expr::Bool(b)) => {
                    *expr = Expr::Bool(!b);
                    *rewrites += 1;
                }
                (
                    UnaryOp::Not,
                    Expr::Unary {
                        op: UnaryOp::Not,
                        expr: dbl,
                    },
                ) => {
                    *expr = (**dbl).clone();
                    *rewrites += 1;
                }
                (
                    UnaryOp::Neg,
                    Expr::Unary {
                        op: UnaryOp::Neg,
                        expr: dbl,
                    },
                ) => {
                    *expr = (**dbl).clone();
                    *rewrites += 1;
                }
                (UnaryOp::Neg, Expr::Int(0)) => {
                    *expr = Expr::Int(0);
                    *rewrites += 1;
                }
                _ => {}
            }
        }
        Expr::Binary { op, left, right } => {
            opt_expr(left, rewrites);
            opt_expr(right, rewrites);

            if let (Some(a), Some(b)) = (const_int(left), const_int(right)) {
                let folded: Option<Expr> = match op {
                    BinOp::Add => a.checked_add(b).map(canonical_int_expr),
                    BinOp::Sub => a.checked_sub(b).map(canonical_int_expr),
                    BinOp::Mul => a.checked_mul(b).map(canonical_int_expr),
                    BinOp::Div | BinOp::IntDiv if b != 0 => a.checked_div(b).map(canonical_int_expr),
                    BinOp::Mod if b != 0 => a.checked_rem(b).map(canonical_int_expr),
                    BinOp::Eq => Some(Expr::Bool(a == b)),
                    BinOp::Ne => Some(Expr::Bool(a != b)),
                    BinOp::Lt => Some(Expr::Bool(a < b)),
                    BinOp::Le => Some(Expr::Bool(a <= b)),
                    BinOp::Gt => Some(Expr::Bool(a > b)),
                    BinOp::Ge => Some(Expr::Bool(a >= b)),
                    _ => None,
                };
                if let Some(new_e) = folded {
                    *expr = new_e;
                    *rewrites += 1;
                    return;
                }
            }

            if let (Expr::Str(a), Expr::Str(b)) = (left.as_ref(), right.as_ref()) {
                if *op == BinOp::Add {
                    *expr = Expr::Str(format!("{}{}", a, b));
                    *rewrites += 1;
                    return;
                }
            }

            if let (Expr::Bool(a), Expr::Bool(b)) = (left.as_ref(), right.as_ref()) {
                let folded = match op {
                    BinOp::And => Some(Expr::Bool(*a && *b)),
                    BinOp::Or => Some(Expr::Bool(*a || *b)),
                    BinOp::Eq => Some(Expr::Bool(a == b)),
                    BinOp::Ne => Some(Expr::Bool(a != b)),
                    _ => None,
                };
                if let Some(new_e) = folded {
                    *expr = new_e;
                    *rewrites += 1;
                    return;
                }
            }

            // Algebraic identities on pure operands
            match (*op, const_int(left), const_int(right)) {
                (BinOp::Add, Some(0), _) => {
                    *expr = (**right).clone();
                    *rewrites += 1;
                }
                (BinOp::Add | BinOp::Sub, _, Some(0)) => {
                    *expr = (**left).clone();
                    *rewrites += 1;
                }
                (BinOp::Mul, Some(1), _) => {
                    *expr = (**right).clone();
                    *rewrites += 1;
                }
                (BinOp::Mul | BinOp::Div | BinOp::IntDiv, _, Some(1)) => {
                    *expr = (**left).clone();
                    *rewrites += 1;
                }
                (BinOp::Mul, Some(0), _) if is_pure_expr(right) => {
                    *expr = Expr::Int(0);
                    *rewrites += 1;
                }
                (BinOp::Mul, _, Some(0)) if is_pure_expr(left) => {
                    *expr = Expr::Int(0);
                    *rewrites += 1;
                }
                _ => {}
            }
        }
        Expr::Intrinsic(intr) => {
            match intr.as_mut() {
                Intrinsic::Len(e)
                | Intrinsic::Abs(e)
                | Intrinsic::Upper(e)
                | Intrinsic::Lower(e)
                | Intrinsic::ToStr(e) => opt_expr(e, rewrites),
                Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                    opt_expr(a, rewrites);
                    opt_expr(b, rewrites);
                }
                Intrinsic::Push { list, value } => {
                    opt_expr(list, rewrites);
                    opt_expr(value, rewrites);
                }
                Intrinsic::Print(args) => {
                    for a in args {
                        opt_expr(a, rewrites);
                    }
                }
                Intrinsic::Contains { haystack, needle } => {
                    opt_expr(haystack, rewrites);
                    opt_expr(needle, rewrites);
                }
            }

            let folded: Option<Expr> = match intr.as_ref() {
                Intrinsic::Min(a, b) => match (const_int(a), const_int(b)) {
                    (Some(x), Some(y)) => Some(canonical_int_expr(x.min(y))),
                    _ => None,
                },
                Intrinsic::Max(a, b) => match (const_int(a), const_int(b)) {
                    (Some(x), Some(y)) => Some(canonical_int_expr(x.max(y))),
                    _ => None,
                },
                Intrinsic::Abs(a) => const_int(a).map(|x| canonical_int_expr(x.abs())),
                Intrinsic::Upper(Expr::Str(s)) => Some(Expr::Str(s.to_uppercase())),
                Intrinsic::Lower(Expr::Str(s)) => Some(Expr::Str(s.to_lowercase())),
                Intrinsic::ToStr(e) => match const_int(e) {
                    Some(v) => Some(Expr::Str(v.to_string())),
                    None => match e {
                        Expr::Bool(b) => {
                            Some(Expr::Str(if *b { "true" } else { "false" }.to_string()))
                        }
                        Expr::Str(s) => Some(Expr::Str(s.clone())),
                        _ => None,
                    },
                },
                _ => None,
            };
            if let Some(new_e) = folded {
                *expr = new_e;
                *rewrites += 1;
            }
        }
        _ => {}
    }
}

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;

pub type NodeId = u64;
pub type Metadata = BTreeMap<String, String>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub language: String,
    pub message: String,
    pub line: usize,
    pub col: usize,
}

impl Diagnostic {
    pub fn new(
        language: impl Into<String>,
        message: impl Into<String>,
        line: usize,
        col: usize,
    ) -> Self {
        Self {
            language: language.into(),
            message: message.into(),
            line,
            col,
        }
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}] line {}, col {}: {}",
            self.language, self.line, self.col, self.message
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Float,
    Bool,
    Str,
    Void,
    List(Box<Type>),
    /// Named user type (`Struct` or `Enum`, resolved from `HubModule`).
    Named(String),
}

impl Type {
    pub fn list(inner: Type) -> Self {
        Type::List(Box::new(inner))
    }

    pub fn display(&self) -> String {
        match self {
            Type::Int => "Int".to_string(),
            Type::Float => "Float".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Str => "Str".to_string(),
            Type::Void => "Void".to_string(),
            Type::List(inner) => format!("List<{}>", inner.display()),
            Type::Named(n) => n.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct HubModule {
    pub items: Vec<Item>,
    pub next_id: NodeId,
}

impl Default for HubModule {
    fn default() -> Self {
        Self {
            items: Vec::new(),
            next_id: 1,
        }
    }
}

impl HubModule {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn find_struct(&self, name: &str) -> Option<&StructDecl> {
        self.items.iter().find_map(|item| match item {
            Item::Struct(s) if s.name == name => Some(s),
            _ => None,
        })
    }

    pub fn find_enum(&self, name: &str) -> Option<&EnumDecl> {
        self.items.iter().find_map(|item| match item {
            Item::Enum(e) if e.name == name => Some(e),
            _ => None,
        })
    }

    pub fn is_enum_name(&self, name: &str) -> bool {
        self.find_enum(name).is_some()
    }

    pub fn find_fn(&self, name: &str) -> Option<&FnDecl> {
        self.items.iter().find_map(|item| match item {
            Item::Function(f) if f.name == name => Some(f),
            _ => None,
        })
    }

    pub fn find_test(&self, name: &str) -> Option<&TestDecl> {
        self.items.iter().find_map(|item| match item {
            Item::Test(t) if t.name == name => Some(t),
            _ => None,
        })
    }

    pub fn has_main(&self) -> bool {
        self.find_fn("main").is_some()
    }

    pub fn node_count(&self) -> usize {
        fn count_stmts(stmts: &[Stmt]) -> usize {
            stmts
                .iter()
                .map(|s| match s {
                    Stmt::If {
                        then_body,
                        else_body,
                        ..
                    } => 1 + count_stmts(then_body) + count_stmts(else_body),
                    Stmt::While { body, .. }
                    | Stmt::ForEach { body, .. }
                    | Stmt::ForRange { body, .. } => 1 + count_stmts(body),
                    Stmt::Match { arms, .. } => {
                        1 + arms.iter().map(|a| count_stmts(&a.body)).sum::<usize>()
                    }
                    _ => 1,
                })
                .sum()
        }

        self.items
            .iter()
            .map(|item| match item {
                Item::Struct(s) => 1 + s.fields.len(),
                Item::Enum(e) => 1 + e.variants.len(),
                Item::Function(f) => 1 + f.params.len() + count_stmts(&f.body),
                Item::Test(t) => 1 + count_stmts(&t.body),
            })
            .sum()
    }

    pub fn test_count(&self) -> usize {
        self.items
            .iter()
            .filter(|i| matches!(i, Item::Test(_)))
            .count()
    }

    pub fn metadata_badges(&self) -> Vec<String> {
        let mut badges = Vec::new();
        for item in &self.items {
            match item {
                Item::Struct(s) => {
                    for (k, v) in &s.meta {
                        badges.push(format!("struct {} #{} [{}={}]", s.name, s.id, k, v));
                    }
                }
                Item::Enum(e) => {
                    for (k, v) in &e.meta {
                        badges.push(format!("enum {} #{} [{}={}]", e.name, e.id, k, v));
                    }
                }
                Item::Function(f) => {
                    for (k, v) in &f.meta {
                        badges.push(format!("fn {} #{} [{}={}]", f.name, f.id, k, v));
                    }
                    for p in &f.params {
                        for (k, v) in &p.meta {
                            badges.push(format!("{}::{} #{} [{}={}]", f.name, p.name, p.id, k, v));
                        }
                    }
                }
                Item::Test(t) => {
                    for (k, v) in &t.meta {
                        badges.push(format!("test {} #{} [{}={}]", t.name, t.id, k, v));
                    }
                }
            }
        }
        badges
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Struct(StructDecl),
    Enum(EnumDecl),
    Function(FnDecl),
    Test(TestDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TestDecl {
    pub id: NodeId,
    pub name: String,
    pub body: Vec<Stmt>,
    pub comments: Vec<String>,
    pub meta: Metadata,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDecl {
    pub id: NodeId,
    pub name: String,
    pub fields: Vec<Field>,
    pub comments: Vec<String>,
    pub meta: Metadata,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub id: NodeId,
    pub name: String,
    pub ty: Type,
    pub meta: Metadata,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumDecl {
    pub id: NodeId,
    pub name: String,
    pub variants: Vec<String>,
    pub comments: Vec<String>,
    pub meta: Metadata,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub id: NodeId,
    pub name: String,
    pub params: Vec<Param>,
    pub ret_ty: Type,
    pub body: Vec<Stmt>,
    pub comments: Vec<String>,
    pub meta: Metadata,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub id: NodeId,
    pub name: String,
    pub ty: Type,
    pub meta: Metadata,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Set,
    AddAssign,
    SubAssign,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AssignTarget {
    Var(String),
    Field { base: String, field: String },
    Index { base: String, index: Expr },
}

impl AssignTarget {
    pub fn root_var(&self) -> &str {
        match self {
            AssignTarget::Var(v) => v,
            AssignTarget::Field { base, .. } => base,
            AssignTarget::Index { base, .. } => base,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchPat {
    EnumVariant { enum_name: String, variant: String },
    Int(i64),
    Str(String),
    Wildcard,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pat: MatchPat,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Comment {
        id: NodeId,
        text: String,
    },
    Let {
        id: NodeId,
        name: String,
        mutable: bool,
        ty: Option<Type>,
        value: Expr,
        meta: Metadata,
    },
    Assign {
        id: NodeId,
        target: AssignTarget,
        op: AssignOp,
        value: Expr,
        meta: Metadata,
    },
    If {
        id: NodeId,
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
        meta: Metadata,
    },
    Match {
        id: NodeId,
        expr: Expr,
        arms: Vec<MatchArm>,
        meta: Metadata,
    },
    While {
        id: NodeId,
        cond: Expr,
        body: Vec<Stmt>,
        meta: Metadata,
    },
    ForEach {
        id: NodeId,
        var: String,
        iter: Expr,
        body: Vec<Stmt>,
        meta: Metadata,
    },
    ForRange {
        id: NodeId,
        var: String,
        start: Expr,
        end: Expr,
        body: Vec<Stmt>,
        meta: Metadata,
    },
    Break {
        id: NodeId,
    },
    Continue {
        id: NodeId,
    },
    Return {
        id: NodeId,
        value: Option<Expr>,
        meta: Metadata,
    },
    Assert {
        id: NodeId,
        cond: Expr,
        meta: Metadata,
    },
    AssertEq {
        id: NodeId,
        left: Expr,
        right: Expr,
        meta: Metadata,
    },
    Expr {
        id: NodeId,
        expr: Expr,
        meta: Metadata,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IntDiv,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Var(String),
    EnumVariant {
        enum_name: String,
        variant: String,
    },
    List(Vec<Expr>),
    StructInit {
        name: String,
        fields: Vec<(String, Expr)>,
    },
    FieldAccess {
        base: Box<Expr>,
        field: String,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        func: String,
        args: Vec<Expr>,
    },
    Intrinsic(Box<Intrinsic>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Intrinsic {
    Len(Expr),
    Min(Expr, Expr),
    Max(Expr, Expr),
    Abs(Expr),
    Push { list: Expr, value: Expr },
    Print(Vec<Expr>),
    Contains { haystack: Expr, needle: Expr },
    Upper(Expr),
    Lower(Expr),
    ToStr(Expr),
}

impl Expr {
    pub fn intrinsic(i: Intrinsic) -> Self {
        Expr::Intrinsic(Box::new(i))
    }
}

pub fn normalize_module(module: &mut HubModule) {
    let mut fn_ret_types: HashMap<String, Type> = HashMap::new();
    let mut struct_fields: HashMap<String, HashMap<String, Type>> = HashMap::new();
    let mut enum_names: HashSet<String> = HashSet::new();

    for item in &module.items {
        match item {
            Item::Function(f) => {
                fn_ret_types.insert(f.name.clone(), f.ret_ty.clone());
            }
            Item::Struct(s) => {
                let mut fields = HashMap::new();
                for fl in &s.fields {
                    fields.insert(fl.name.clone(), fl.ty.clone());
                }
                struct_fields.insert(s.name.clone(), fields);
            }
            Item::Enum(e) => {
                enum_names.insert(e.name.clone());
            }
            Item::Test(_) => {}
        }
    }

    for item in &mut module.items {
        match item {
            Item::Function(func) => {
                let mut mutated = HashSet::new();
                collect_mutated_vars(&func.body, &mut mutated);

                let mut env: HashMap<String, Type> = HashMap::new();
                for p in &func.params {
                    env.insert(p.name.clone(), p.ty.clone());
                }

                let mut list_elem_hints: HashMap<String, Type> = HashMap::new();
                collect_list_hints(
                    &func.body,
                    &func.ret_ty,
                    &env,
                    &fn_ret_types,
                    &struct_fields,
                    &enum_names,
                    &mut list_elem_hints,
                );

                normalize_block(
                    &mut func.body,
                    &mutated,
                    &mut env,
                    &list_elem_hints,
                    &fn_ret_types,
                    &struct_fields,
                    &enum_names,
                );
            }
            Item::Test(test) => {
                while let Some(stripped) = test.name.strip_prefix("test_") {
                    if stripped.is_empty() {
                        break;
                    }
                    test.name = stripped.to_string();
                }
                let mut mutated = HashSet::new();
                collect_mutated_vars(&test.body, &mut mutated);
                let mut env: HashMap<String, Type> = HashMap::new();
                let mut list_elem_hints: HashMap<String, Type> = HashMap::new();
                collect_list_hints(
                    &test.body,
                    &Type::Void,
                    &env,
                    &fn_ret_types,
                    &struct_fields,
                    &enum_names,
                    &mut list_elem_hints,
                );
                normalize_block(
                    &mut test.body,
                    &mutated,
                    &mut env,
                    &list_elem_hints,
                    &fn_ret_types,
                    &struct_fields,
                    &enum_names,
                );
            }
            _ => {}
        }
    }
}

fn collect_mutated_vars(stmts: &[Stmt], out: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Assign { target, .. } => {
                out.insert(target.root_var().to_string());
            }
            Stmt::Expr { expr, .. } | Stmt::Let { value: expr, .. } => {
                collect_mutated_in_expr(expr, out);
            }
            Stmt::Return {
                value: Some(expr), ..
            } => collect_mutated_in_expr(expr, out),
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                collect_mutated_in_expr(cond, out);
                collect_mutated_vars(then_body, out);
                collect_mutated_vars(else_body, out);
            }
            Stmt::Match { expr, arms, .. } => {
                collect_mutated_in_expr(expr, out);
                for arm in arms {
                    collect_mutated_vars(&arm.body, out);
                }
            }
            Stmt::While { cond, body, .. } => {
                collect_mutated_in_expr(cond, out);
                collect_mutated_vars(body, out);
            }
            Stmt::ForEach { iter, body, .. } => {
                collect_mutated_in_expr(iter, out);
                collect_mutated_vars(body, out);
            }
            Stmt::ForRange {
                start, end, body, ..
            } => {
                collect_mutated_in_expr(start, out);
                collect_mutated_in_expr(end, out);
                collect_mutated_vars(body, out);
            }
            Stmt::Assert { cond, .. } => {
                collect_mutated_in_expr(cond, out);
            }
            Stmt::AssertEq { left, right, .. } => {
                collect_mutated_in_expr(left, out);
                collect_mutated_in_expr(right, out);
            }
            _ => {}
        }
    }
}

fn collect_mutated_in_expr(expr: &Expr, out: &mut HashSet<String>) {
    if let Expr::Intrinsic(intr) = expr {
        if let Intrinsic::Push { list, value } = intr.as_ref() {
            if let Expr::Var(v) = list {
                out.insert(v.clone());
            }
            collect_mutated_in_expr(value, out);
        }
    }
}

fn collect_list_hints(
    stmts: &[Stmt],
    ret_ty: &Type,
    env: &HashMap<String, Type>,
    fn_ret_types: &HashMap<String, Type>,
    struct_fields: &HashMap<String, HashMap<String, Type>>,
    enum_names: &HashSet<String>,
    hints: &mut HashMap<String, Type>,
) {
    let mut local_env = env.clone();
    for stmt in stmts {
        match stmt {
            Stmt::Let {
                name, ty, value, ..
            } => {
                if let Some(t) = ty {
                    local_env.insert(name.clone(), t.clone());
                } else if let Some(t) =
                    infer_expr_type(value, &local_env, fn_ret_types, struct_fields, enum_names)
                {
                    local_env.insert(name.clone(), t);
                }
            }
            Stmt::Expr {
                expr: Expr::Intrinsic(intr),
                ..
            } => {
                if let Intrinsic::Push {
                    list: Expr::Var(v),
                    value,
                } = intr.as_ref()
                {
                    if let Some(val_ty) =
                        infer_expr_type(value, &local_env, fn_ret_types, struct_fields, enum_names)
                    {
                        hints.entry(v.clone()).or_insert(val_ty);
                    }
                }
            }
            Stmt::Return {
                value: Some(Expr::Var(v)),
                ..
            } => {
                if let Type::List(inner) = ret_ty {
                    hints.entry(v.clone()).or_insert((**inner).clone());
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_list_hints(
                    then_body,
                    ret_ty,
                    &local_env,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                    hints,
                );
                collect_list_hints(
                    else_body,
                    ret_ty,
                    &local_env,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                    hints,
                );
            }
            Stmt::Match { arms, .. } => {
                for arm in arms {
                    collect_list_hints(
                        &arm.body,
                        ret_ty,
                        &local_env,
                        fn_ret_types,
                        struct_fields,
                        enum_names,
                        hints,
                    );
                }
            }
            Stmt::While { body, .. } => {
                collect_list_hints(
                    body,
                    ret_ty,
                    &local_env,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                    hints,
                );
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let mut inner_env = local_env.clone();
                if let Some(Type::List(elem)) =
                    infer_expr_type(iter, &local_env, fn_ret_types, struct_fields, enum_names)
                {
                    inner_env.insert(var.clone(), *elem);
                }
                collect_list_hints(
                    body,
                    ret_ty,
                    &inner_env,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                    hints,
                );
            }
            Stmt::ForRange { var, body, .. } => {
                let mut inner_env = local_env.clone();
                inner_env.insert(var.clone(), Type::Int);
                collect_list_hints(
                    body,
                    ret_ty,
                    &inner_env,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                    hints,
                );
            }
            _ => {}
        }
    }
}

fn normalize_block(
    stmts: &mut [Stmt],
    mutated: &HashSet<String>,
    env: &mut HashMap<String, Type>,
    list_elem_hints: &HashMap<String, Type>,
    fn_ret_types: &HashMap<String, Type>,
    struct_fields: &HashMap<String, HashMap<String, Type>>,
    enum_names: &HashSet<String>,
) {
    for stmt in stmts {
        match stmt {
            Stmt::Let {
                name,
                mutable,
                ty,
                value,
                meta,
                ..
            } => {
                normalize_expr(value, env, fn_ret_types, struct_fields, enum_names);
                if mutated.contains(name) {
                    *mutable = true;
                    meta.remove("explicit_mut");
                } else if meta.get("explicit_mut").map(|s| s.as_str()) == Some("true") {
                    *mutable = true;
                } else {
                    *mutable = false;
                }

                if ty.is_none() {
                    if let Expr::List(items) = value {
                        if items.is_empty() {
                            if let Some(elem_ty) = list_elem_hints.get(name) {
                                *ty = Some(Type::list(elem_ty.clone()));
                            } else {
                                *ty = Some(Type::list(Type::Int));
                            }
                        }
                    }
                }

                if let Some(t) = ty {
                    env.insert(name.clone(), t.clone());
                } else if let Some(t) =
                    infer_expr_type(value, env, fn_ret_types, struct_fields, enum_names)
                {
                    env.insert(name.clone(), t);
                }
            }
            Stmt::Assign { value, .. } => {
                normalize_expr(value, env, fn_ret_types, struct_fields, enum_names);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                normalize_expr(cond, env, fn_ret_types, struct_fields, enum_names);
                let mut then_env = env.clone();
                normalize_block(
                    then_body,
                    mutated,
                    &mut then_env,
                    list_elem_hints,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                );
                let mut else_env = env.clone();
                normalize_block(
                    else_body,
                    mutated,
                    &mut else_env,
                    list_elem_hints,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                );
            }
            Stmt::Match { expr, arms, .. } => {
                normalize_expr(expr, env, fn_ret_types, struct_fields, enum_names);
                for arm in arms {
                    let mut arm_env = env.clone();
                    normalize_block(
                        &mut arm.body,
                        mutated,
                        &mut arm_env,
                        list_elem_hints,
                        fn_ret_types,
                        struct_fields,
                        enum_names,
                    );
                }
            }
            Stmt::While { cond, body, .. } => {
                normalize_expr(cond, env, fn_ret_types, struct_fields, enum_names);
                let mut body_env = env.clone();
                normalize_block(
                    body,
                    mutated,
                    &mut body_env,
                    list_elem_hints,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                );
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                normalize_expr(iter, env, fn_ret_types, struct_fields, enum_names);
                let mut body_env = env.clone();
                if let Some(Type::List(elem)) =
                    infer_expr_type(iter, env, fn_ret_types, struct_fields, enum_names)
                {
                    body_env.insert(var.clone(), *elem);
                }
                normalize_block(
                    body,
                    mutated,
                    &mut body_env,
                    list_elem_hints,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                );
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                normalize_expr(start, env, fn_ret_types, struct_fields, enum_names);
                normalize_expr(end, env, fn_ret_types, struct_fields, enum_names);
                let mut body_env = env.clone();
                body_env.insert(var.clone(), Type::Int);
                normalize_block(
                    body,
                    mutated,
                    &mut body_env,
                    list_elem_hints,
                    fn_ret_types,
                    struct_fields,
                    enum_names,
                );
            }
            Stmt::Return {
                value: Some(expr), ..
            } => {
                normalize_expr(expr, env, fn_ret_types, struct_fields, enum_names);
            }
            Stmt::Assert { id, cond, meta } => {
                normalize_expr(cond, env, fn_ret_types, struct_fields, enum_names);
                // Canonicalize `assert(a == b)` into `AssertEq(a, b)` across all spokes!
                if let Expr::Binary {
                    op: BinOp::Eq,
                    left,
                    right,
                } = cond
                {
                    let nid = *id;
                    let nmeta = meta.clone();
                    let l = (**left).clone();
                    let r = (**right).clone();
                    *stmt = Stmt::AssertEq {
                        id: nid,
                        left: l,
                        right: r,
                        meta: nmeta,
                    };
                }
            }
            Stmt::AssertEq { left, right, .. } => {
                normalize_expr(left, env, fn_ret_types, struct_fields, enum_names);
                normalize_expr(right, env, fn_ret_types, struct_fields, enum_names);
            }
            Stmt::Expr { expr, .. } => {
                normalize_expr(expr, env, fn_ret_types, struct_fields, enum_names);
            }
            Stmt::Return { value: None, .. }
            | Stmt::Comment { .. }
            | Stmt::Break { .. }
            | Stmt::Continue { .. } => {}
        }
    }
}

fn normalize_expr(
    expr: &mut Expr,
    env: &HashMap<String, Type>,
    fn_ret_types: &HashMap<String, Type>,
    struct_fields: &HashMap<String, HashMap<String, Type>>,
    enum_names: &HashSet<String>,
) {
    // Convert `FieldAccess { Var("Grade"), "A" }` parsed by Python/TS into `Expr::EnumVariant`
    if let Expr::FieldAccess { base, field } = expr {
        if let Expr::Var(maybe_enum) = base.as_ref() {
            if enum_names.contains(maybe_enum) {
                *expr = Expr::EnumVariant {
                    enum_name: maybe_enum.clone(),
                    variant: field.clone(),
                };
                return;
            }
        }
    }

    match expr {
        Expr::List(items) => {
            for it in items {
                normalize_expr(it, env, fn_ret_types, struct_fields, enum_names);
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, v) in fields {
                normalize_expr(v, env, fn_ret_types, struct_fields, enum_names);
            }
        }
        Expr::FieldAccess { base, .. } => {
            normalize_expr(base, env, fn_ret_types, struct_fields, enum_names);
        }
        Expr::Index { base, index } => {
            normalize_expr(base, env, fn_ret_types, struct_fields, enum_names);
            normalize_expr(index, env, fn_ret_types, struct_fields, enum_names);
        }
        Expr::Unary { expr: inner, .. } => {
            normalize_expr(inner, env, fn_ret_types, struct_fields, enum_names);
        }
        Expr::Binary { op, left, right } => {
            normalize_expr(left, env, fn_ret_types, struct_fields, enum_names);
            normalize_expr(right, env, fn_ret_types, struct_fields, enum_names);
            if *op == BinOp::Div {
                let lt = infer_expr_type(left, env, fn_ret_types, struct_fields, enum_names);
                let rt = infer_expr_type(right, env, fn_ret_types, struct_fields, enum_names);
                if lt == Some(Type::Int) && rt == Some(Type::Int) {
                    *op = BinOp::IntDiv;
                }
            }
        }
        Expr::Call { args, .. } => {
            for a in args {
                normalize_expr(a, env, fn_ret_types, struct_fields, enum_names);
            }
        }
        Expr::Intrinsic(intr) => {
            match intr.as_mut() {
                Intrinsic::Len(e)
                | Intrinsic::Abs(e)
                | Intrinsic::Upper(e)
                | Intrinsic::Lower(e)
                | Intrinsic::ToStr(e) => {
                    normalize_expr(e, env, fn_ret_types, struct_fields, enum_names);
                }
                Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                    normalize_expr(a, env, fn_ret_types, struct_fields, enum_names);
                    normalize_expr(b, env, fn_ret_types, struct_fields, enum_names);
                }
                Intrinsic::Push { list, value } => {
                    normalize_expr(list, env, fn_ret_types, struct_fields, enum_names);
                    normalize_expr(value, env, fn_ret_types, struct_fields, enum_names);
                }
                Intrinsic::Print(args) => {
                    for a in args {
                        normalize_expr(a, env, fn_ret_types, struct_fields, enum_names);
                    }
                }
                Intrinsic::Contains { haystack, needle } => {
                    normalize_expr(haystack, env, fn_ret_types, struct_fields, enum_names);
                    normalize_expr(needle, env, fn_ret_types, struct_fields, enum_names);
                }
            }
            // Disambiguate Swift `.count` or TS/Ruby `.length` on a struct field vs `Array`/`String` len
            if let Intrinsic::Len(inner) = intr.as_ref() {
                if let Some(Type::Named(sname)) =
                    infer_expr_type(inner, env, fn_ret_types, struct_fields, enum_names)
                {
                    if struct_fields
                        .get(&sname)
                        .map(|m| m.contains_key("count"))
                        .unwrap_or(false)
                    {
                        *expr = Expr::FieldAccess {
                            base: Box::new(inner.clone()),
                            field: "count".to_string(),
                        };
                    } else if struct_fields
                        .get(&sname)
                        .map(|m| m.contains_key("length"))
                        .unwrap_or(false)
                    {
                        *expr = Expr::FieldAccess {
                            base: Box::new(inner.clone()),
                            field: "length".to_string(),
                        };
                    } else if struct_fields
                        .get(&sname)
                        .map(|m| m.contains_key("len"))
                        .unwrap_or(false)
                    {
                        *expr = Expr::FieldAccess {
                            base: Box::new(inner.clone()),
                            field: "len".to_string(),
                        };
                    }
                }
            }
        }
        Expr::Int(v) if *v < 0 && *v > i64::MIN => {
            let pos = -*v;
            *expr = Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(Expr::Int(pos)),
            };
        }
        Expr::Float(v) if *v < 0.0 => {
            let pos = -*v;
            *expr = Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(Expr::Float(pos)),
            };
        }
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Bool(_)
        | Expr::Str(_)
        | Expr::Var(_)
        | Expr::EnumVariant { .. } => {}
    }
}

pub fn infer_expr_type(
    expr: &Expr,
    env: &HashMap<String, Type>,
    fn_ret_types: &HashMap<String, Type>,
    struct_fields: &HashMap<String, HashMap<String, Type>>,
    enum_names: &HashSet<String>,
) -> Option<Type> {
    match expr {
        Expr::Int(_) => Some(Type::Int),
        Expr::Float(_) => Some(Type::Float),
        Expr::Bool(_) => Some(Type::Bool),
        Expr::Str(_) => Some(Type::Str),
        Expr::Var(name) => env.get(name).cloned(),
        Expr::EnumVariant { enum_name, .. } => Some(Type::Named(enum_name.clone())),
        Expr::List(items) => {
            let first = items.first()?;
            let inner = infer_expr_type(first, env, fn_ret_types, struct_fields, enum_names)?;
            Some(Type::list(inner))
        }
        Expr::StructInit { name, .. } => Some(Type::Named(name.clone())),
        Expr::FieldAccess { base, field } => {
            if let Expr::Var(maybe_enum) = base.as_ref() {
                if enum_names.contains(maybe_enum) {
                    return Some(Type::Named(maybe_enum.clone()));
                }
            }
            if let Some(Type::Named(sname)) =
                infer_expr_type(base, env, fn_ret_types, struct_fields, enum_names)
            {
                struct_fields.get(&sname)?.get(field).cloned()
            } else {
                None
            }
        }
        Expr::Index { base, .. } => {
            if let Some(Type::List(inner)) =
                infer_expr_type(base, env, fn_ret_types, struct_fields, enum_names)
            {
                Some(*inner)
            } else {
                None
            }
        }
        Expr::Unary { op, expr } => match op {
            UnaryOp::Neg => infer_expr_type(expr, env, fn_ret_types, struct_fields, enum_names),
            UnaryOp::Not => Some(Type::Bool),
        },
        Expr::Binary { op, left, right } => match op {
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or => Some(Type::Bool),
            BinOp::IntDiv | BinOp::Mod => Some(Type::Int),
            BinOp::Div => Some(Type::Float),
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                infer_expr_type(left, env, fn_ret_types, struct_fields, enum_names).or_else(|| {
                    infer_expr_type(right, env, fn_ret_types, struct_fields, enum_names)
                })
            }
        },
        Expr::Call { func, .. } => fn_ret_types.get(func).cloned(),
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(_) => Some(Type::Int),
            Intrinsic::Min(a, _) | Intrinsic::Max(a, _) | Intrinsic::Abs(a) => {
                infer_expr_type(a, env, fn_ret_types, struct_fields, enum_names)
            }
            Intrinsic::Push { .. } | Intrinsic::Print(_) => Some(Type::Void),
            Intrinsic::Contains { .. } => Some(Type::Bool),
            Intrinsic::Upper(_) | Intrinsic::Lower(_) | Intrinsic::ToStr(_) => Some(Type::Str),
        },
    }
}

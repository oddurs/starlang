use std::collections::{BTreeSet, HashMap, HashSet};

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl,
    HubModule, Intrinsic, Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl,
    Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct GoLens;

impl LanguageLens for GoLens {
    fn id(&self) -> SpokeId {
        SpokeId::Go
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut ctx = GoFmtCtx::from_hub(hub);
        let imports = ctx.collect_imports(hub);

        let mut out = String::new();
        out.push_str("package main\n");

        if imports.len() == 1 {
            let imp = imports.iter().next().unwrap();
            out.push_str(&format!("\nimport \"{}\"\n", imp));
        } else if imports.len() > 1 {
            out.push_str("\nimport (\n");
            for imp in &imports {
                out.push_str(&format!("\t\"{}\"\n", imp));
            }
            out.push_str(")\n");
        }

        for item in &hub.items {
            out.push('\n');
            match item {
                Item::Struct(s) => ctx.fmt_struct(s, &mut out),
                Item::Enum(e) => ctx.fmt_enum(e, &mut out),
                Item::Function(f) => ctx.fmt_fn(f, &mut out),
                Item::Test(t) => ctx.fmt_test(t, &mut out),
            }
        }
        out
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_go(source)?;
        let mut known_enums: HashSet<String> = HashSet::new();
        for item in &prev_hub.items {
            if let Item::Enum(e) = item {
                known_enums.insert(e.name.clone());
            }
        }
        let mut parser = GoParser {
            tokens,
            pos: 0,
            allow_struct_lit: true,
            known_enums,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Go))
    }
}

struct GoFmtCtx {
    fn_ret_types: HashMap<String, Type>,
    struct_fields: HashMap<String, HashMap<String, Type>>,
    enum_names: HashSet<String>,
    local_env: HashMap<String, Type>,
}

impl GoFmtCtx {
    fn from_hub(hub: &HubModule) -> Self {
        let mut fn_ret_types = HashMap::new();
        let mut struct_fields = HashMap::new();
        let mut enum_names = HashSet::new();
        for item in &hub.items {
            match item {
                Item::Function(f) => {
                    fn_ret_types.insert(f.name.clone(), f.ret_ty.clone());
                }
                Item::Struct(s) => {
                    let mut fmap = HashMap::new();
                    for fl in &s.fields {
                        fmap.insert(fl.name.clone(), fl.ty.clone());
                    }
                    struct_fields.insert(s.name.clone(), fmap);
                }
                Item::Enum(e) => {
                    enum_names.insert(e.name.clone());
                }
                Item::Test(_) => {}
            }
        }
        Self {
            fn_ret_types,
            struct_fields,
            enum_names,
            local_env: HashMap::new(),
        }
    }

    fn expr_ty(&self, expr: &Expr) -> Option<Type> {
        infer_expr_type(
            expr,
            &self.local_env,
            &self.fn_ret_types,
            &self.struct_fields,
            &self.enum_names,
        )
    }

    fn collect_imports(&mut self, hub: &HubModule) -> BTreeSet<&'static str> {
        let mut imports = BTreeSet::new();
        for item in &hub.items {
            match item {
                Item::Function(f) => {
                    self.local_env.clear();
                    for p in &f.params {
                        self.local_env.insert(p.name.clone(), p.ty.clone());
                    }
                    self.scan_stmts_imports(&f.body, &mut imports);
                }
                Item::Test(t) => {
                    self.local_env.clear();
                    self.scan_stmts_imports(&t.body, &mut imports);
                }
                _ => {}
            }
        }
        imports
    }

    fn scan_stmts_imports(&mut self, stmts: &[Stmt], imports: &mut BTreeSet<&'static str>) {
        for s in stmts {
            match s {
                Stmt::Let {
                    name, ty, value, ..
                } => {
                    self.scan_expr_imports(value, imports);
                    if let Some(t) = ty.clone().or_else(|| self.expr_ty(value)) {
                        self.local_env.insert(name.clone(), t);
                    }
                }
                Stmt::Assign { value, .. } => self.scan_expr_imports(value, imports),
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    self.scan_expr_imports(cond, imports);
                    let saved = self.local_env.clone();
                    self.scan_stmts_imports(then_body, imports);
                    self.local_env = saved.clone();
                    self.scan_stmts_imports(else_body, imports);
                    self.local_env = saved;
                }
                Stmt::Match { expr, arms, .. } => {
                    self.scan_expr_imports(expr, imports);
                    for arm in arms {
                        let saved = self.local_env.clone();
                        self.scan_stmts_imports(&arm.body, imports);
                        self.local_env = saved;
                    }
                }
                Stmt::While { cond, body, .. } => {
                    self.scan_expr_imports(cond, imports);
                    let saved = self.local_env.clone();
                    self.scan_stmts_imports(body, imports);
                    self.local_env = saved;
                }
                Stmt::ForEach {
                    var, iter, body, ..
                } => {
                    self.scan_expr_imports(iter, imports);
                    let saved = self.local_env.clone();
                    if let Some(Type::List(elem)) = self.expr_ty(iter) {
                        self.local_env.insert(var.clone(), *elem);
                    }
                    self.scan_stmts_imports(body, imports);
                    self.local_env = saved;
                }
                Stmt::ForRange {
                    var,
                    start,
                    end,
                    body,
                    ..
                } => {
                    self.scan_expr_imports(start, imports);
                    self.scan_expr_imports(end, imports);
                    let saved = self.local_env.clone();
                    self.local_env.insert(var.clone(), Type::Int);
                    self.scan_stmts_imports(body, imports);
                    self.local_env = saved;
                }
                Stmt::Assert { cond, .. } => self.scan_expr_imports(cond, imports),
                Stmt::AssertEq { left, right, .. } => {
                    imports.insert("reflect");
                    self.scan_expr_imports(left, imports);
                    self.scan_expr_imports(right, imports);
                }
                Stmt::Return {
                    value: Some(e), ..
                }
                | Stmt::Expr { expr: e, .. } => self.scan_expr_imports(e, imports),
                _ => {}
            }
        }
    }

    fn scan_expr_imports(&self, expr: &Expr, imports: &mut BTreeSet<&'static str>) {
        match expr {
            Expr::List(items) => {
                for it in items {
                    self.scan_expr_imports(it, imports);
                }
            }
            Expr::StructInit { fields, .. } => {
                for (_, v) in fields {
                    self.scan_expr_imports(v, imports);
                }
            }
            Expr::FieldAccess { base, .. } => self.scan_expr_imports(base, imports),
            Expr::Index { base, index } => {
                self.scan_expr_imports(base, imports);
                self.scan_expr_imports(index, imports);
            }
            Expr::Unary { expr: inner, .. } => self.scan_expr_imports(inner, imports),
            Expr::Binary { left, right, .. } => {
                self.scan_expr_imports(left, imports);
                self.scan_expr_imports(right, imports);
            }
            Expr::Call { args, .. } => {
                for a in args {
                    self.scan_expr_imports(a, imports);
                }
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Print(args) => {
                    imports.insert("fmt");
                    for a in args {
                        self.scan_expr_imports(a, imports);
                    }
                }
                Intrinsic::ToStr(e) => {
                    imports.insert("fmt");
                    self.scan_expr_imports(e, imports);
                }
                Intrinsic::Abs(e) => {
                    imports.insert("math");
                    self.scan_expr_imports(e, imports);
                }
                Intrinsic::Upper(e) | Intrinsic::Lower(e) => {
                    imports.insert("strings");
                    self.scan_expr_imports(e, imports);
                }
                Intrinsic::Contains { haystack, needle } => {
                    if matches!(self.expr_ty(haystack), Some(Type::List(_))) {
                        imports.insert("slices");
                    } else {
                        imports.insert("strings");
                    }
                    self.scan_expr_imports(haystack, imports);
                    self.scan_expr_imports(needle, imports);
                }
                Intrinsic::Len(e) => self.scan_expr_imports(e, imports),
                Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                    self.scan_expr_imports(a, imports);
                    self.scan_expr_imports(b, imports);
                }
                Intrinsic::Push { list, value } => {
                    self.scan_expr_imports(list, imports);
                    self.scan_expr_imports(value, imports);
                }
            },
            _ => {}
        }
    }

    fn fmt_type(ty: &Type) -> String {
        match ty {
            Type::Int => "int64".to_string(),
            Type::Float => "float64".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Str => "string".to_string(),
            Type::Void => "".to_string(),
            Type::List(inner) => format!("[]{}", Self::fmt_type(inner)),
            Type::Named(name) => name.clone(),
        }
    }

    fn fmt_struct(&self, s: &StructDecl, out: &mut String) {
        for c in &s.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("type {} struct {{\n", s.name));
        for f in &s.fields {
            out.push_str(&format!("\t{} {}\n", f.name, Self::fmt_type(&f.ty)));
        }
        out.push_str("}\n");
    }

    fn fmt_enum(&self, e: &EnumDecl, out: &mut String) {
        for c in &e.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("type {} int64\n\nconst (\n", e.name));
        for (i, v) in e.variants.iter().enumerate() {
            if i == 0 {
                out.push_str(&format!("\t{}_{} {} = iota\n", e.name, v, e.name));
            } else {
                out.push_str(&format!("\t{}_{}\n", e.name, v));
            }
        }
        out.push_str(")\n");
    }

    fn fmt_fn(&mut self, f: &FnDecl, out: &mut String) {
        for c in &f.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        for p in &f.params {
            self.local_env.insert(p.name.clone(), p.ty.clone());
        }
        let params_str: Vec<String> = f
            .params
            .iter()
            .map(|p| format!("{} {}", p.name, Self::fmt_type(&p.ty)))
            .collect();
        if f.ret_ty == Type::Void {
            out.push_str(&format!("func {}({}) {{\n", f.name, params_str.join(", ")));
        } else {
            out.push_str(&format!(
                "func {}({}) {} {{\n",
                f.name,
                params_str.join(", "),
                Self::fmt_type(&f.ret_ty)
            ));
        }
        for s in &f.body {
            self.fmt_stmt(s, 1, out);
        }
        if f.ret_ty != Type::Void && !go_block_terminates(&f.body) {
            out.push_str("\tpanic(\"unreachable\")\n");
        }
        out.push_str("}\n");
    }

    fn fmt_test(&mut self, t: &TestDecl, out: &mut String) {
        for c in &t.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        out.push_str(&format!("func test_{}() {{\n", t.name));
        for s in &t.body {
            self.fmt_stmt(s, 1, out);
        }
        out.push_str("}\n");
    }

    fn fmt_pat(&self, pat: &MatchPat) -> String {
        match pat {
            MatchPat::EnumVariant { enum_name, variant } => format!("{}_{}", enum_name, variant),
            MatchPat::Int(v) => v.to_string(),
            MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
            MatchPat::Wildcard => "default".to_string(),
        }
    }

    fn fmt_stmt(&mut self, stmt: &Stmt, indent: usize, out: &mut String) {
        let pad = "\t".repeat(indent);
        match stmt {
            Stmt::Comment { text, .. } => {
                out.push_str(&format!("{}// {}\n", pad, text));
            }
            Stmt::Let {
                name, ty, value, ..
            } => {
                if let Some(t) = ty {
                    let val_str = match (t, value) {
                        (Type::List(_), Expr::List(items)) if items.is_empty() => {
                            format!("{}{{}}", Self::fmt_type(t))
                        }
                        _ => self.fmt_expr(value),
                    };
                    self.local_env.insert(name.clone(), t.clone());
                    out.push_str(&format!(
                        "{}var {} {} = {}\n",
                        pad,
                        name,
                        Self::fmt_type(t),
                        val_str
                    ));
                } else {
                    if let Some(inferred) = self.expr_ty(value) {
                        self.local_env.insert(name.clone(), inferred);
                    }
                    out.push_str(&format!("{}{} := {}\n", pad, name, self.fmt_expr(value)));
                }
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let op_str = match op {
                    AssignOp::Set => "=",
                    AssignOp::AddAssign => "+=",
                    AssignOp::SubAssign => "-=",
                };
                let tgt = match target {
                    AssignTarget::Var(v) => v.clone(),
                    AssignTarget::Field { base, field } => format!("{}.{}", base, field),
                    AssignTarget::Index { base, index } => {
                        format!("{}[{}]", base, self.fmt_expr(index))
                    }
                };
                out.push_str(&format!("{}{} {} {}\n", pad, tgt, op_str, self.fmt_expr(value)));
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.fmt_if_chain(cond, then_body, else_body, indent, true, out);
            }
            Stmt::Match { expr, arms, .. } => {
                out.push_str(&format!("{}switch {} {{\n", pad, self.fmt_expr(expr)));
                for arm in arms {
                    if arm.pat == MatchPat::Wildcard {
                        out.push_str(&format!("{}default:\n", pad));
                    } else {
                        out.push_str(&format!("{}case {}:\n", pad, self.fmt_pat(&arm.pat)));
                    }
                    let saved = self.local_env.clone();
                    for s in &arm.body {
                        self.fmt_stmt(s, indent + 1, out);
                    }
                    self.local_env = saved;
                }
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::While { cond, body, .. } => {
                out.push_str(&format!("{}for {} {{\n", pad, self.fmt_expr(cond)));
                let saved = self.local_env.clone();
                for s in body {
                    self.fmt_stmt(s, indent + 1, out);
                }
                self.local_env = saved;
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                out.push_str(&format!(
                    "{}for _, {} := range {} {{\n",
                    pad,
                    var,
                    self.fmt_expr(iter)
                ));
                let saved = self.local_env.clone();
                if let Some(Type::List(elem)) = self.expr_ty(iter) {
                    self.local_env.insert(var.clone(), *elem);
                }
                for s in body {
                    self.fmt_stmt(s, indent + 1, out);
                }
                self.local_env = saved;
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                out.push_str(&format!(
                    "{}for {} := {}; {} < {}; {}++ {{\n",
                    pad,
                    var,
                    self.fmt_expr(start),
                    var,
                    self.fmt_clean_int(end),
                    var
                ));
                let saved = self.local_env.clone();
                self.local_env.insert(var.clone(), Type::Int);
                for s in body {
                    self.fmt_stmt(s, indent + 1, out);
                }
                self.local_env = saved;
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::Break { .. } => out.push_str(&format!("{}break\n", pad)),
            Stmt::Continue { .. } => out.push_str(&format!("{}continue\n", pad)),
            Stmt::Return { value, .. } => match value {
                Some(v) => out.push_str(&format!("{}return {}\n", pad, self.fmt_expr(v))),
                None => out.push_str(&format!("{}return\n", pad)),
            },
            Stmt::Assert { cond, .. } => {
                out.push_str(&format!(
                    "{}if !({}) {{\n{}\tpanic(\"assertion failed\")\n{}}}\n",
                    pad,
                    self.fmt_expr(cond),
                    pad,
                    pad
                ));
            }
            Stmt::AssertEq { left, right, .. } => {
                let fmt_side = |side: &Expr, peer: &Expr| -> String {
                    if let Expr::List(items) = side {
                        if items.is_empty() {
                            if let Some(Type::List(elem)) = self.expr_ty(peer) {
                                return format!("[]{}{{}}", Self::fmt_type(&elem));
                            }
                        }
                    }
                    self.fmt_expr(side)
                };
                out.push_str(&format!(
                    "{}if !reflect.DeepEqual({}, {}) {{\n{}\tpanic(\"assert_eq failed\")\n{}}}\n",
                    pad,
                    fmt_side(left, right),
                    fmt_side(right, left),
                    pad,
                    pad
                ));
            }
            Stmt::Expr { expr, .. } => {
                out.push_str(&format!("{}{}\n", pad, self.fmt_expr(expr)));
            }
        }
    }

    fn fmt_if_chain(
        &mut self,
        cond: &Expr,
        then_body: &[Stmt],
        else_body: &[Stmt],
        indent: usize,
        first: bool,
        out: &mut String,
    ) {
        let pad = "\t".repeat(indent);
        if first {
            out.push_str(&format!("{}if {} {{\n", pad, self.fmt_expr(cond)));
        } else {
            out.push_str(&format!(" else if {} {{\n", self.fmt_expr(cond)));
        }
        let saved = self.local_env.clone();
        for s in then_body {
            self.fmt_stmt(s, indent + 1, out);
        }
        self.local_env = saved;

        if else_body.is_empty() {
            out.push_str(&format!("{}}}\n", pad));
        } else if else_body.len() == 1 && matches!(&else_body[0], Stmt::If { .. }) {
            out.push_str(&format!("{}}}", pad));
            if let Stmt::If {
                cond: c2,
                then_body: t2,
                else_body: e2,
                ..
            } = &else_body[0]
            {
                self.fmt_if_chain(c2, t2, e2, indent, false, out);
            }
        } else {
            out.push_str(&format!("{}}} else {{\n", pad));
            let saved2 = self.local_env.clone();
            for s in else_body {
                self.fmt_stmt(s, indent + 1, out);
            }
            self.local_env = saved2;
            out.push_str(&format!("{}}}\n", pad));
        }
    }

    fn fmt_postfix(&self, expr: &Expr) -> String {
        let s = self.fmt_expr(expr);
        match expr {
            Expr::Binary { .. } | Expr::Unary { .. } => format!("({})", s),
            _ => s,
        }
    }

    fn fmt_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => format!("int64({})", v),
            Expr::Float(v) => format_float(*v),
            Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Expr::Str(s) => format!("\"{}\"", escape_str(s)),
            Expr::Var(v) => v.clone(),
            Expr::EnumVariant { enum_name, variant } => format!("{}_{}", enum_name, variant),
            Expr::List(items) => {
                let elem_ty = items
                    .first()
                    .and_then(|e| self.expr_ty(e))
                    .unwrap_or(Type::Int);
                let inner: Vec<String> = items.iter().map(|e| self.fmt_list_elem(e)).collect();
                format!("[]{}{{{}}}", Self::fmt_type(&elem_ty), inner.join(", "))
            }
            Expr::StructInit { name, fields } => {
                let inner: Vec<String> = fields
                    .iter()
                    .map(|(fname, fval)| format!("{}: {}", fname, self.fmt_expr(fval)))
                    .collect();
                format!("{}{{{}}}", name, inner.join(", "))
            }
            Expr::FieldAccess { base, field } => format!("{}.{}", self.fmt_postfix(base), field),
            Expr::Index { base, index } => {
                format!("{}[{}]", self.fmt_postfix(base), self.fmt_clean_int(index))
            }
            Expr::Unary { op, expr: inner } => {
                if *op == UnaryOp::Neg {
                    if let Expr::Int(v) = inner.as_ref() {
                        return format!("int64(-{})", v);
                    }
                }
                let sym = match op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "!",
                };
                match inner.as_ref() {
                    Expr::Binary { .. } | Expr::Unary { .. } => {
                        format!("{}({})", sym, self.fmt_expr(inner))
                    }
                    _ => format!("{}{}", sym, self.fmt_expr(inner)),
                }
            }
            Expr::Binary { op, left, right } => {
                let l_raw = self.fmt_clean_int(left);
                let r_raw = self.fmt_clean_int(right);
                let l_str = if needs_parens(left, *op, false) {
                    format!("({})", l_raw)
                } else {
                    l_raw
                };
                let r_str = if needs_parens(right, *op, true) {
                    format!("({})", r_raw)
                } else {
                    r_raw
                };
                let op_str = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div | BinOp::IntDiv => "/",
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
                // If both sides are untyped int literals in an arithmetic expr, wrap result in int64(...)
                let is_int_lit = |e: &Expr| {
                    matches!(e, Expr::Int(_))
                        || matches!(
                            e,
                            Expr::Unary {
                                op: UnaryOp::Neg,
                                expr: inner
                            } if matches!(inner.as_ref(), Expr::Int(_))
                        )
                };
                let both_int_lits = is_int_lit(left)
                    && is_int_lit(right)
                    && matches!(
                        op,
                        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::IntDiv | BinOp::Mod
                    );
                if both_int_lits {
                    format!("int64({} {} {})", l_str, op_str, r_str)
                } else {
                    format!("{} {} {}", l_str, op_str, r_str)
                }
            }
            Expr::Call { func, args } => {
                let inner: Vec<String> = args.iter().map(|a| self.fmt_expr(a)).collect();
                format!("{}({})", func, inner.join(", "))
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e) => format!("int64(len({}))", self.fmt_expr(e)),
                Intrinsic::Min(a, b) => {
                    format!("min({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Max(a, b) => {
                    format!("max({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Abs(a) => {
                    if self.expr_ty(a) == Some(Type::Float) {
                        format!("math.Abs({})", self.fmt_expr(a))
                    } else {
                        format!("int64(math.Abs(float64({})))", self.fmt_expr(a))
                    }
                }
                Intrinsic::Push { list, value } => {
                    let l = self.fmt_expr(list);
                    format!("{} = append({}, {})", l, l, self.fmt_expr(value))
                }
                Intrinsic::Print(args) => {
                    let inner: Vec<String> =
                        args.iter().map(|a| self.fmt_clean_int(a)).collect();
                    format!("fmt.Println({})", inner.join(", "))
                }
                Intrinsic::Contains { haystack, needle } => {
                    if matches!(self.expr_ty(haystack), Some(Type::List(_))) {
                        format!(
                            "slices.Contains({}, {})",
                            self.fmt_expr(haystack),
                            self.fmt_expr(needle)
                        )
                    } else {
                        format!(
                            "strings.Contains({}, {})",
                            self.fmt_expr(haystack),
                            self.fmt_expr(needle)
                        )
                    }
                }
                Intrinsic::Upper(e) => format!("strings.ToUpper({})", self.fmt_expr(e)),
                Intrinsic::Lower(e) => format!("strings.ToLower({})", self.fmt_expr(e)),
                Intrinsic::ToStr(e) => format!("fmt.Sprintf(\"%v\", {})", self.fmt_clean_int(e)),
            },
        }
    }

    fn fmt_clean_int(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => v.to_string(),
            Expr::Unary {
                op: UnaryOp::Neg,
                expr: inner,
            } if matches!(inner.as_ref(), Expr::Int(_)) => {
                if let Expr::Int(v) = inner.as_ref() {
                    format!("-{}", v)
                } else {
                    unreachable!()
                }
            }
            _ => self.fmt_expr(expr),
        }
    }

    fn fmt_list_elem(&self, expr: &Expr) -> String {
        self.fmt_clean_int(expr)
    }
}

// ============================================================================
// Go Lexer & Recursive-Descent Parser (`put`)
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
enum GTokKind {
    Ident(String),
    Int(i64),
    Float(f64),
    Str(String),
    Comment(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semi,
    Colon,
    ColonEq,
    Dot,
    Plus,
    PlusPlus,
    Minus,
    Star,
    Slash,
    Percent,
    AmpAmp,
    PipePipe,
    Bang,
    Eq,
    EqEq,
    BangEq,
    Lt,
    Le,
    Gt,
    Ge,
    PlusEq,
    MinusEq,
}

#[derive(Debug, Clone)]
struct GTok {
    kind: GTokKind,
    line: usize,
    col: usize,
}

fn lex_go(src: &str) -> Result<Vec<GTok>, Diagnostic> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut line = 1;
    let mut col = 1;

    while i < chars.len() {
        let ch = chars[i];
        if ch == '\n' {
            i += 1;
            line += 1;
            col = 1;
            continue;
        }
        if ch.is_whitespace() {
            i += 1;
            col += 1;
            continue;
        }
        if ch == '/' && i + 1 < chars.len() && chars[i + 1] == '/' {
            let s_col = col;
            i += 2;
            col += 2;
            if i < chars.len() && chars[i] == ' ' {
                i += 1;
                col += 1;
            }
            let start = i;
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
                col += 1;
            }
            let text: String = chars[start..i].iter().collect();
            tokens.push(GTok {
                kind: GTokKind::Comment(text),
                line,
                col: s_col,
            });
            continue;
        }
        if ch == '"' {
            let s_line = line;
            let s_col = col;
            i += 1;
            col += 1;
            let mut raw = String::new();
            let mut closed = false;
            while i < chars.len() {
                let c = chars[i];
                if c == '"' {
                    i += 1;
                    col += 1;
                    closed = true;
                    break;
                }
                if c == '\\' && i + 1 < chars.len() {
                    raw.push('\\');
                    raw.push(chars[i + 1]);
                    i += 2;
                    col += 2;
                    continue;
                }
                if c == '\n' {
                    line += 1;
                    col = 1;
                } else {
                    col += 1;
                }
                raw.push(c);
                i += 1;
            }
            if !closed {
                return Err(Diagnostic::new(
                    "go",
                    "unterminated string literal",
                    s_line,
                    s_col,
                ));
            }
            tokens.push(GTok {
                kind: GTokKind::Str(unescape_string(&raw)),
                line: s_line,
                col: s_col,
            });
            continue;
        }
        if ch.is_ascii_digit() {
            let s_col = col;
            let start = i;
            let mut is_float = false;
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            if i + 1 < chars.len() && chars[i] == '.' && chars[i + 1].is_ascii_digit() {
                is_float = true;
                i += 1;
                col += 1;
                while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                    i += 1;
                    col += 1;
                }
            }
            let num_str: String = chars[start..i].iter().filter(|c| **c != '_').collect();
            if is_float {
                let v = num_str
                    .parse::<f64>()
                    .map_err(|_| Diagnostic::new("go", "invalid float literal", line, s_col))?;
                tokens.push(GTok {
                    kind: GTokKind::Float(v),
                    line,
                    col: s_col,
                });
            } else {
                let v = num_str
                    .parse::<i64>()
                    .map_err(|_| Diagnostic::new("go", "invalid int literal", line, s_col))?;
                tokens.push(GTok {
                    kind: GTokKind::Int(v),
                    line,
                    col: s_col,
                });
            }
            continue;
        }
        if ch.is_ascii_alphabetic() || ch == '_' {
            let s_col = col;
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            let ident: String = chars[start..i].iter().collect();
            tokens.push(GTok {
                kind: GTokKind::Ident(ident),
                line,
                col: s_col,
            });
            continue;
        }

        let s_col = col;
        if i + 1 < chars.len() {
            let two = match (chars[i], chars[i + 1]) {
                (':', '=') => Some(GTokKind::ColonEq),
                ('+', '+') => Some(GTokKind::PlusPlus),
                ('&', '&') => Some(GTokKind::AmpAmp),
                ('|', '|') => Some(GTokKind::PipePipe),
                ('=', '=') => Some(GTokKind::EqEq),
                ('!', '=') => Some(GTokKind::BangEq),
                ('<', '=') => Some(GTokKind::Le),
                ('>', '=') => Some(GTokKind::Ge),
                ('+', '=') => Some(GTokKind::PlusEq),
                ('-', '=') => Some(GTokKind::MinusEq),
                _ => None,
            };
            if let Some(kind) = two {
                tokens.push(GTok {
                    kind,
                    line,
                    col: s_col,
                });
                i += 2;
                col += 2;
                continue;
            }
        }

        let kind = match ch {
            '(' => GTokKind::LParen,
            ')' => GTokKind::RParen,
            '{' => GTokKind::LBrace,
            '}' => GTokKind::RBrace,
            '[' => GTokKind::LBracket,
            ']' => GTokKind::RBracket,
            ',' => GTokKind::Comma,
            ';' => GTokKind::Semi,
            ':' => GTokKind::Colon,
            '.' => GTokKind::Dot,
            '+' => GTokKind::Plus,
            '-' => GTokKind::Minus,
            '*' => GTokKind::Star,
            '/' => GTokKind::Slash,
            '%' => GTokKind::Percent,
            '!' => GTokKind::Bang,
            '=' => GTokKind::Eq,
            '<' => GTokKind::Lt,
            '>' => GTokKind::Gt,
            other => {
                return Err(Diagnostic::new(
                    "go",
                    format!("unexpected character '{}'", other),
                    line,
                    s_col,
                ))
            }
        };
        tokens.push(GTok {
            kind,
            line,
            col: s_col,
        });
        i += 1;
        col += 1;
    }

    Ok(tokens)
}

struct GoParser {
    tokens: Vec<GTok>,
    pos: usize,
    allow_struct_lit: bool,
    known_enums: HashSet<String>,
}

impl GoParser {
    fn peek(&self) -> Option<&GTok> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&GTokKind> {
        self.peek().map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<GTok> {
        let tok = self.tokens.get(self.pos).cloned();
        if tok.is_some() {
            self.pos += 1;
        }
        tok
    }

    fn err<T>(&self, msg: impl Into<String>) -> Result<T, Diagnostic> {
        let (line, col) = self
            .peek()
            .map(|t| (t.line, t.col))
            .or_else(|| self.tokens.last().map(|t| (t.line, t.col)))
            .unwrap_or((1, 1));
        Err(Diagnostic::new("go", msg, line, col))
    }

    fn eat(&mut self, expected: &GTokKind) -> bool {
        if self.peek_kind() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if matches!(self.peek_kind(), Some(GTokKind::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &GTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(expected) {
            Ok(())
        } else {
            self.err(format!("expected {}", label))
        }
    }

    fn expect_ident(&mut self) -> Result<String, Diagnostic> {
        match self.next() {
            Some(GTok {
                kind: GTokKind::Ident(s),
                ..
            }) => Ok(s),
            _ => self.err("expected identifier"),
        }
    }

    fn split_enum_const(&self, ident: &str) -> Option<(String, String)> {
        let (ename, vname) = ident.split_once('_')?;
        if self.known_enums.contains(ename) && !vname.is_empty() {
            Some((ename.to_string(), vname.to_string()))
        } else {
            None
        }
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut module = HubModule::new();
        let mut comments = Vec::new();

        while self.peek().is_some() {
            if let Some(GTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.next();
                comments.push(c);
                continue;
            }
            if self.eat(&GTokKind::Semi) {
                continue;
            }
            if self.eat_kw("package") {
                let _ = self.expect_ident()?;
                let _ = self.eat(&GTokKind::Semi);
                continue;
            }
            if self.eat_kw("import") {
                if self.eat(&GTokKind::LParen) {
                    while !matches!(self.peek_kind(), Some(GTokKind::RParen) | None) {
                        self.next();
                    }
                    self.expect(&GTokKind::RParen, "')'")?;
                } else {
                    self.next();
                }
                continue;
            }

            let item_comments = std::mem::take(&mut comments);
            if self.eat_kw("type") {
                let name = self.expect_ident()?;
                if self.eat_kw("struct") {
                    let s = self.parse_struct(name, item_comments)?;
                    module.items.push(Item::Struct(s));
                } else {
                    // Enum alias `type Status int64` followed by `const ( Status_Ok Status = iota ... )`
                    let _ = self.parse_type()?;
                    self.known_enums.insert(name.clone());
                    let variants = self.parse_enum_const_block(&name)?;
                    module.items.push(Item::Enum(EnumDecl {
                        id: 0,
                        name,
                        variants,
                        comments: item_comments,
                        meta: Metadata::new(),
                    }));
                }
            } else if self.eat_kw("func") {
                let f = self.parse_fn(item_comments)?;
                if f.params.is_empty() && f.ret_ty == Type::Void {
                    if let Some(tname) = f.name.strip_prefix("test_") {
                        if !tname.is_empty() {
                            module.items.push(Item::Test(TestDecl {
                                id: 0,
                                name: tname.to_string(),
                                body: f.body,
                                comments: f.comments,
                                meta: f.meta,
                            }));
                            continue;
                        }
                    }
                }
                module.items.push(Item::Function(f));
            } else {
                return self.err("expected 'type' or 'func' at top level in Go");
            }
        }

        Ok(module)
    }

    fn parse_struct(&mut self, name: String, comments: Vec<String>) -> Result<StructDecl, Diagnostic> {
        self.expect(&GTokKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), Some(GTokKind::RBrace) | None) {
            if let Some(GTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            let fname = self.expect_ident()?;
            let fty = self.parse_type()?;
            let _ = self.eat(&GTokKind::Semi);
            fields.push(Field {
                id: 0,
                name: fname,
                ty: fty,
                meta: Metadata::new(),
            });
        }
        self.expect(&GTokKind::RBrace, "'}'")?;
        Ok(StructDecl {
            id: 0,
            name,
            fields,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_enum_const_block(&mut self, enum_name: &str) -> Result<Vec<String>, Diagnostic> {
        let mut variants = Vec::new();
        if self.eat_kw("const") {
            self.expect(&GTokKind::LParen, "'(' after const")?;
            let prefix = format!("{}_", enum_name);
            while !matches!(self.peek_kind(), Some(GTokKind::RParen) | None) {
                if let Some(GTokKind::Comment(_)) = self.peek_kind() {
                    self.next();
                    continue;
                }
                let ident = self.expect_ident()?;
                let vname = ident.strip_prefix(&prefix).unwrap_or(&ident).to_string();
                variants.push(vname);
                // Optional `<EnumName> = iota` or `= <int>`
                if matches!(self.peek_kind(), Some(GTokKind::Ident(s)) if s == enum_name) {
                    self.next();
                }
                if self.eat(&GTokKind::Eq) {
                    let _ = self.parse_expr()?;
                }
                let _ = self.eat(&GTokKind::Semi);
            }
            self.expect(&GTokKind::RParen, "')'")?;
        }
        Ok(variants)
    }

    fn parse_fn(&mut self, comments: Vec<String>) -> Result<FnDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&GTokKind::LParen, "'('")?;
        let mut params = Vec::new();
        while !matches!(self.peek_kind(), Some(GTokKind::RParen) | None) {
            let pname = self.expect_ident()?;
            let pty = self.parse_type()?;
            params.push(Param {
                id: 0,
                name: pname,
                ty: pty,
                meta: Metadata::new(),
            });
            if !self.eat(&GTokKind::Comma) {
                break;
            }
        }
        self.expect(&GTokKind::RParen, "')'")?;

        let ret_ty = if matches!(self.peek_kind(), Some(GTokKind::LBrace)) {
            Type::Void
        } else {
            self.parse_type()?
        };

        let mut body = self.parse_block()?;
        if ret_ty != Type::Void {
            let strip_unreachable = matches!(
                body.last(),
                Some(Stmt::Expr {
                    expr: Expr::Call { func, args },
                    ..
                }) if func == "panic"
                    && args.len() == 1
                    && matches!(&args[0], Expr::Str(msg) if msg == "unreachable")
            );
            if strip_unreachable {
                body.pop();
            }
        }
        Ok(FnDecl {
            id: 0,
            name,
            params,
            ret_ty,
            body,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_type(&mut self) -> Result<Type, Diagnostic> {
        if self.eat(&GTokKind::LBracket) {
            self.expect(&GTokKind::RBracket, "']'")?;
            let inner = self.parse_type()?;
            return Ok(Type::list(inner));
        }
        let ident = self.expect_ident()?;
        Ok(match ident.as_str() {
            "int" | "int64" | "int32" => Type::Int,
            "float64" | "float32" => Type::Float,
            "bool" => Type::Bool,
            "string" => Type::Str,
            other => Type::Named(other.to_string()),
        })
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        self.expect(&GTokKind::LBrace, "'{'")?;
        let mut stmts = Vec::new();
        while !matches!(self.peek_kind(), Some(GTokKind::RBrace) | None) {
            stmts.push(self.parse_stmt()?);
            let _ = self.eat(&GTokKind::Semi);
        }
        self.expect(&GTokKind::RBrace, "'}'")?;
        Ok(stmts)
    }

    fn parse_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        if let Some(GTokKind::Comment(c)) = self.peek_kind().cloned() {
            self.next();
            return Ok(Stmt::Comment { id: 0, text: c });
        }
        if self.eat_kw("var") {
            let name = self.expect_ident()?;
            let ty = if !matches!(self.peek_kind(), Some(GTokKind::Eq)) {
                Some(self.parse_type()?)
            } else {
                None
            };
            self.expect(&GTokKind::Eq, "'=' in var declaration")?;
            let value = self.parse_expr()?;
            return Ok(Stmt::Let {
                id: 0,
                name,
                mutable: false,
                ty,
                value,
                meta: Metadata::new(),
            });
        }
        if self.eat_kw("if") {
            return self.parse_if();
        }
        if self.eat_kw("switch") {
            return self.parse_switch();
        }
        if self.eat_kw("for") {
            return self.parse_for();
        }
        if self.eat_kw("break") {
            return Ok(Stmt::Break { id: 0 });
        }
        if self.eat_kw("continue") {
            return Ok(Stmt::Continue { id: 0 });
        }
        if self.eat_kw("return") {
            if matches!(
                self.peek_kind(),
                Some(GTokKind::RBrace)
                    | Some(GTokKind::Semi)
                    | Some(GTokKind::Ident(_))
                        if matches!(self.peek_kind(), Some(GTokKind::Ident(k)) if k == "case" || k == "default")
            ) {
                return Ok(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                });
            }
            if matches!(self.peek_kind(), Some(GTokKind::RBrace) | Some(GTokKind::Semi)) {
                return Ok(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                });
            }
            let val = self.parse_expr()?;
            return Ok(Stmt::Return {
                id: 0,
                value: Some(val),
                meta: Metadata::new(),
            });
        }

        let expr = self.parse_expr()?;
        if self.eat(&GTokKind::ColonEq) {
            let Expr::Var(name) = expr else {
                return self.err("expected identifier before ':='");
            };
            let value = self.parse_expr()?;
            return Ok(Stmt::Let {
                id: 0,
                name,
                mutable: false,
                ty: None,
                value,
                meta: Metadata::new(),
            });
        }

        if let Some(op) = match self.peek_kind() {
            Some(GTokKind::Eq) => Some(AssignOp::Set),
            Some(GTokKind::PlusEq) => Some(AssignOp::AddAssign),
            Some(GTokKind::MinusEq) => Some(AssignOp::SubAssign),
            _ => None,
        } {
            self.next();
            let value = self.parse_expr()?;
            // Recognize `list = append(list, val)` -> `Intrinsic::Push`
            if op == AssignOp::Set {
                if let (Expr::Var(lhs), Expr::Call { func, mut args }) = (&expr, value.clone()) {
                    if func == "append" && args.len() == 2 {
                        let pushed_val = args.pop().unwrap();
                        let list_arg = args.pop().unwrap();
                        if list_arg == Expr::Var(lhs.clone()) {
                            return Ok(Stmt::Expr {
                                id: 0,
                                expr: Expr::intrinsic(Intrinsic::Push {
                                    list: list_arg,
                                    value: pushed_val,
                                }),
                                meta: Metadata::new(),
                            });
                        }
                    }
                }
            }
            let target = go_expr_to_target(expr)?;
            return Ok(Stmt::Assign {
                id: 0,
                target,
                op,
                value,
                meta: Metadata::new(),
            });
        }

        Ok(Stmt::Expr {
            id: 0,
            expr,
            meta: Metadata::new(),
        })
    }

    fn parse_if(&mut self) -> Result<Stmt, Diagnostic> {
        let cond = self.parse_header_expr()?;
        let then_body = self.parse_block()?;
        let else_body = if self.eat_kw("else") {
            if self.eat_kw("if") {
                vec![self.parse_if()?]
            } else {
                self.parse_block()?
            }
        } else {
            Vec::new()
        };
        if else_body.is_empty()
            && then_body.len() == 1
            && matches!(
                &then_body[0],
                Stmt::Expr {
                    expr: Expr::Call { func, .. },
                    ..
                } if func == "panic"
            )
        {
            if let Expr::Unary {
                op: UnaryOp::Not,
                expr: inner,
            } = cond
            {
                return Ok(Stmt::Assert {
                    id: 0,
                    cond: *inner,
                    meta: Metadata::new(),
                });
            }
        }
        Ok(Stmt::If {
            id: 0,
            cond,
            then_body,
            else_body,
            meta: Metadata::new(),
        })
    }

    fn parse_switch(&mut self) -> Result<Stmt, Diagnostic> {
        let expr = self.parse_header_expr()?;
        self.expect(&GTokKind::LBrace, "'{' after switch")?;
        let mut arms = Vec::new();
        while !matches!(self.peek_kind(), Some(GTokKind::RBrace) | None) {
            if matches!(self.peek_kind(), Some(GTokKind::Comment(_))) {
                self.next();
                continue;
            }
            let pat = if self.eat_kw("default") {
                self.expect(&GTokKind::Colon, "':' after default")?;
                MatchPat::Wildcard
            } else if self.eat_kw("case") {
                let pexpr = self.parse_expr()?;
                self.expect(&GTokKind::Colon, "':' after case pattern")?;
                match pexpr {
                    Expr::EnumVariant { enum_name, variant } => {
                        MatchPat::EnumVariant { enum_name, variant }
                    }
                    Expr::Int(v) => MatchPat::Int(v),
                    Expr::Unary {
                        op: UnaryOp::Neg,
                        expr: inner,
                    } if matches!(*inner, Expr::Int(_)) => {
                        if let Expr::Int(v) = *inner {
                            MatchPat::Int(-v)
                        } else {
                            unreachable!()
                        }
                    }
                    Expr::Str(s) => MatchPat::Str(s),
                    _ => return self.err("unsupported Go switch case pattern"),
                }
            } else {
                return self.err("expected 'case' or 'default' in switch");
            };

            let mut body = Vec::new();
            while !matches!(self.peek_kind(), Some(GTokKind::RBrace) | None)
                && !matches!(
                    self.peek_kind(),
                    Some(GTokKind::Ident(s)) if s == "case" || s == "default"
                )
            {
                body.push(self.parse_stmt()?);
                let _ = self.eat(&GTokKind::Semi);
            }
            arms.push(MatchArm { pat, body });
        }
        self.expect(&GTokKind::RBrace, "'}'")?;
        Ok(Stmt::Match {
            id: 0,
            expr,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_for(&mut self) -> Result<Stmt, Diagnostic> {
        // Case 1: `for _, x := range iter { ... }` or `for x := range iter`
        if matches!(self.peek_kind(), Some(GTokKind::Ident(_))) {
            let saved = self.pos;
            let first_ident = self.expect_ident()?;
            if self.eat(&GTokKind::Comma) {
                let var = self.expect_ident()?;
                self.expect(&GTokKind::ColonEq, "':='")?;
                if !self.eat_kw("range") {
                    return self.err("expected 'range' in Go for-each loop");
                }
                let iter = self.parse_header_expr()?;
                let body = self.parse_block()?;
                return Ok(Stmt::ForEach {
                    id: 0,
                    var,
                    iter,
                    body,
                    meta: Metadata::new(),
                });
            }
            // Case 2: `for i := start; i < end; i++ { ... }`
            if self.eat(&GTokKind::ColonEq) {
                let start = self.parse_header_expr()?;
                self.expect(&GTokKind::Semi, "';' in Go for-range loop")?;
                let cvar = self.expect_ident()?;
                if cvar != first_ident {
                    return self.err("for-loop condition variable must match loop variable");
                }
                self.expect(&GTokKind::Lt, "'<' in Go for-range loop")?;
                let end = self.parse_header_expr()?;
                self.expect(&GTokKind::Semi, "';' in Go for-range loop")?;
                let _ = self.expect_ident()?;
                if !self.eat(&GTokKind::PlusPlus) && self.eat(&GTokKind::PlusEq) {
                    let _ = self.parse_header_expr()?;
                }
                let body = self.parse_block()?;
                return Ok(Stmt::ForRange {
                    id: 0,
                    var: first_ident,
                    start,
                    end,
                    body,
                    meta: Metadata::new(),
                });
            }
            self.pos = saved;
        }

        // Case 3: `for cond { ... }` -> `While`
        let cond = self.parse_header_expr()?;
        let body = self.parse_block()?;
        Ok(Stmt::While {
            id: 0,
            cond,
            body,
            meta: Metadata::new(),
        })
    }

    fn parse_header_expr(&mut self) -> Result<Expr, Diagnostic> {
        let prev = self.allow_struct_lit;
        self.allow_struct_lit = false;
        let res = self.parse_expr();
        self.allow_struct_lit = prev;
        res
    }

    fn parse_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_and()?;
        while self.eat(&GTokKind::PipePipe) {
            let right = self.parse_and()?;
            left = Expr::Binary {
                op: BinOp::Or,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_cmp()?;
        while self.eat(&GTokKind::AmpAmp) {
            let right = self.parse_cmp()?;
            left = Expr::Binary {
                op: BinOp::And,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_cmp(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_add()?;
        loop {
            let op = match self.peek_kind() {
                Some(GTokKind::EqEq) => Some(BinOp::Eq),
                Some(GTokKind::BangEq) => Some(BinOp::Ne),
                Some(GTokKind::Lt) => Some(BinOp::Lt),
                Some(GTokKind::Le) => Some(BinOp::Le),
                Some(GTokKind::Gt) => Some(BinOp::Gt),
                Some(GTokKind::Ge) => Some(BinOp::Ge),
                _ => None,
            };
            if let Some(op) = op {
                self.next();
                let right = self.parse_add()?;
                left = Expr::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_add(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_mul()?;
        loop {
            let op = match self.peek_kind() {
                Some(GTokKind::Plus) => Some(BinOp::Add),
                Some(GTokKind::Minus) => Some(BinOp::Sub),
                _ => None,
            };
            if let Some(op) = op {
                self.next();
                let right = self.parse_mul()?;
                left = Expr::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_mul(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_unary()?;
        loop {
            let op = match self.peek_kind() {
                Some(GTokKind::Star) => Some(BinOp::Mul),
                Some(GTokKind::Slash) => Some(BinOp::Div),
                Some(GTokKind::Percent) => Some(BinOp::Mod),
                _ => None,
            };
            if let Some(op) = op {
                self.next();
                let right = self.parse_unary()?;
                left = Expr::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Expr, Diagnostic> {
        if self.eat(&GTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        if self.eat(&GTokKind::Bang) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Not,
                expr: Box::new(inner),
            });
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut base = self.parse_primary()?;
        loop {
            if self.eat(&GTokKind::Dot) {
                let member = self.expect_ident()?;
                if self.eat(&GTokKind::LParen) {
                    let mut args = self.parse_expr_list(&GTokKind::RParen)?;
                    base = match (&base, member.as_str(), args.len()) {
                        (Expr::Var(pkg), "Println", _) if pkg == "fmt" => {
                            Expr::intrinsic(Intrinsic::Print(args))
                        }
                        (Expr::Var(pkg), "Sprintf", 2) if pkg == "fmt" => {
                            let val = args.pop().unwrap();
                            Expr::intrinsic(Intrinsic::ToStr(val))
                        }
                        (Expr::Var(pkg), "Abs", 1) if pkg == "math" => {
                            Expr::intrinsic(Intrinsic::Abs(args.pop().unwrap()))
                        }
                        (Expr::Var(pkg), "Contains", 2) if pkg == "strings" || pkg == "slices" => {
                            let needle = args.pop().unwrap();
                            let haystack = args.pop().unwrap();
                            Expr::intrinsic(Intrinsic::Contains { haystack, needle })
                        }
                        (Expr::Var(pkg), "ToUpper", 1) if pkg == "strings" => {
                            Expr::intrinsic(Intrinsic::Upper(args.pop().unwrap()))
                        }
                        (Expr::Var(pkg), "ToLower", 1) if pkg == "strings" => {
                            Expr::intrinsic(Intrinsic::Lower(args.pop().unwrap()))
                        }
                        (Expr::Var(pkg), "DeepEqual", 2) if pkg == "reflect" => {
                            let right = args.pop().unwrap();
                            let left = args.pop().unwrap();
                            Expr::Binary {
                                op: BinOp::Eq,
                                left: Box::new(left),
                                right: Box::new(right),
                            }
                        }
                        _ => {
                            return self.err(format!(
                                "unsupported Go selector call '.{}(...)'",
                                member
                            ))
                        }
                    };
                } else {
                    base = Expr::FieldAccess {
                        base: Box::new(base),
                        field: member,
                    };
                }
            } else if self.eat(&GTokKind::LBracket) {
                let prev = self.allow_struct_lit;
                self.allow_struct_lit = true;
                let idx = self.parse_expr()?;
                self.allow_struct_lit = prev;
                self.expect(&GTokKind::RBracket, "']'")?;
                base = Expr::Index {
                    base: Box::new(base),
                    index: Box::new(idx),
                };
            } else {
                break;
            }
        }
        Ok(base)
    }

    fn parse_primary(&mut self) -> Result<Expr, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(GTokKind::Int(v)) => {
                self.next();
                Ok(Expr::Int(v))
            }
            Some(GTokKind::Float(v)) => {
                self.next();
                Ok(Expr::Float(v))
            }
            Some(GTokKind::Str(s)) => {
                self.next();
                Ok(Expr::Str(s))
            }
            Some(GTokKind::LParen) => {
                self.next();
                let prev = self.allow_struct_lit;
                self.allow_struct_lit = true;
                let e = self.parse_expr()?;
                self.allow_struct_lit = prev;
                self.expect(&GTokKind::RParen, "')'")?;
                Ok(e)
            }
            // Go slice literal `[]int64{1, 2, 3}`
            Some(GTokKind::LBracket) => {
                let _ = self.parse_type()?;
                self.expect(&GTokKind::LBrace, "'{' in Go slice literal")?;
                let items = self.parse_expr_list(&GTokKind::RBrace)?;
                Ok(Expr::List(items))
            }
            Some(GTokKind::Ident(ident)) => {
                self.next();
                if ident == "true" {
                    return Ok(Expr::Bool(true));
                }
                if ident == "false" {
                    return Ok(Expr::Bool(false));
                }
                if let Some((ename, vname)) = self.split_enum_const(&ident) {
                    return Ok(Expr::EnumVariant {
                        enum_name: ename,
                        variant: vname,
                    });
                }
                if self.eat(&GTokKind::LParen) {
                    let mut args = self.parse_expr_list(&GTokKind::RParen)?;
                    return match (ident.as_str(), args.len()) {
                        ("int64" | "int" | "float64", 1) => Ok(args.pop().unwrap()),
                        ("len", 1) => Ok(Expr::intrinsic(Intrinsic::Len(args.pop().unwrap()))),
                        ("min", 2) => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            Ok(Expr::intrinsic(Intrinsic::Min(a, b)))
                        }
                        ("max", 2) => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            Ok(Expr::intrinsic(Intrinsic::Max(a, b)))
                        }
                        _ => Ok(Expr::Call { func: ident, args }),
                    };
                }
                // Struct literal `Summary{count: 1, ...}`
                if self.allow_struct_lit
                    && ident
                        .chars()
                        .next()
                        .map(|c| c.is_ascii_uppercase())
                        .unwrap_or(false)
                    && self.eat(&GTokKind::LBrace)
                {
                    let mut fields = Vec::new();
                    while !matches!(self.peek_kind(), Some(GTokKind::RBrace) | None) {
                        let fname = self.expect_ident()?;
                        self.expect(&GTokKind::Colon, "':' in Go struct literal")?;
                        let prev = self.allow_struct_lit;
                        self.allow_struct_lit = true;
                        let fval = self.parse_expr()?;
                        self.allow_struct_lit = prev;
                        fields.push((fname, fval));
                        if !self.eat(&GTokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&GTokKind::RBrace, "'}'")?;
                    return Ok(Expr::StructInit {
                        name: ident,
                        fields,
                    });
                }
                Ok(Expr::Var(ident))
            }
            _ => self.err("expected Go expression"),
        }
    }

    fn parse_expr_list(&mut self, closing: &GTokKind) -> Result<Vec<Expr>, Diagnostic> {
        let prev = self.allow_struct_lit;
        self.allow_struct_lit = true;
        let mut items = Vec::new();
        while self.peek_kind() != Some(closing) && self.peek().is_some() {
            items.push(self.parse_expr()?);
            if !self.eat(&GTokKind::Comma) {
                break;
            }
        }
        self.allow_struct_lit = prev;
        self.expect(closing, "closing ')' or '}'")?;
        Ok(items)
    }
}

fn go_expr_to_target(expr: Expr) -> Result<AssignTarget, Diagnostic> {
    match expr {
        Expr::Var(v) => Ok(AssignTarget::Var(v)),
        Expr::FieldAccess { base, field } => {
            if let Expr::Var(b) = *base {
                Ok(AssignTarget::Field { base: b, field })
            } else {
                Err(Diagnostic::new(
                    "go",
                    "nested field assignment not supported",
                    1,
                    1,
                ))
            }
        }
        Expr::Index { base, index } => {
            if let Expr::Var(b) = *base {
                Ok(AssignTarget::Index {
                    base: b,
                    index: *index,
                })
            } else {
                Err(Diagnostic::new(
                    "go",
                    "nested index assignment not supported",
                    1,
                    1,
                ))
            }
        }
        _ => Err(Diagnostic::new("go", "invalid assignment target", 1, 1)),
    }
}

fn go_block_terminates(stmts: &[Stmt]) -> bool {
    stmts
        .iter()
        .rev()
        .find(|s| !matches!(s, Stmt::Comment { .. }))
        .map(go_stmt_terminates)
        .unwrap_or(false)
}

fn go_stmt_terminates(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Return { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            !else_body.is_empty()
                && go_block_terminates(then_body)
                && go_block_terminates(else_body)
        }
        Stmt::Match { arms, .. } => {
            arms.iter().any(|a| a.pat == MatchPat::Wildcard)
                && arms
                    .iter()
                    .all(|a| go_block_terminates(&a.body) && !go_stmts_have_break(&a.body))
        }
        _ => false,
    }
}

fn go_stmts_have_break(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Break { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => go_stmts_have_break(then_body) || go_stmts_have_break(else_body),
        _ => false,
    })
}

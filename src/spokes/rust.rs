use std::collections::{HashMap, HashSet};

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl,
    HubModule, Intrinsic, Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl,
    Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct RustLens;

impl LanguageLens for RustLens {
    fn id(&self) -> SpokeId {
        SpokeId::Rust
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut ctx = RustFmtCtx::from_hub(hub);
        let mut out = String::new();
        for (idx, item) in hub.items.iter().enumerate() {
            if idx > 0 {
                out.push('\n');
            }
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
        let tokens = lex_rust(source)?;
        let mut parser = RustParser {
            tokens,
            pos: 0,
            allow_struct_lit: true,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Rust))
    }
}

type RustFnSig = (Vec<(Type, Option<String>)>, Type);

struct RustFmtCtx {
    fn_sigs: HashMap<String, RustFnSig>,
    fn_ret_types: HashMap<String, Type>,
    struct_fields: HashMap<String, HashMap<String, Type>>,
    enum_names: HashSet<String>,
    local_env: HashMap<String, Type>,
    borrowed_locals: HashSet<String>,
}

impl RustFmtCtx {
    fn from_hub(hub: &HubModule) -> Self {
        let mut fn_sigs = HashMap::new();
        let mut fn_ret_types = HashMap::new();
        let mut struct_fields = HashMap::new();
        let mut enum_names = HashSet::new();
        for item in &hub.items {
            match item {
                Item::Function(f) => {
                    let params = f
                        .params
                        .iter()
                        .map(|p| (p.ty.clone(), p.meta.get("rust.pass").cloned()))
                        .collect();
                    fn_sigs.insert(f.name.clone(), (params, f.ret_ty.clone()));
                    fn_ret_types.insert(f.name.clone(), f.ret_ty.clone());
                }
                Item::Struct(s) => {
                    let mut map = HashMap::new();
                    for fl in &s.fields {
                        map.insert(fl.name.clone(), fl.ty.clone());
                    }
                    struct_fields.insert(s.name.clone(), map);
                }
                Item::Enum(e) => {
                    enum_names.insert(e.name.clone());
                }
                Item::Test(_) => {}
            }
        }
        Self {
            fn_sigs,
            fn_ret_types,
            struct_fields,
            enum_names,
            local_env: HashMap::new(),
            borrowed_locals: HashSet::new(),
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

    fn target_ty(&self, target: &AssignTarget) -> Option<Type> {
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
        self.expr_ty(&target_expr)
    }

    fn is_copy_ty(&self, ty: &Type) -> bool {
        match ty {
            Type::Int | Type::Float | Type::Bool | Type::Void => true,
            Type::Named(n) => self.enum_names.contains(n),
            Type::Str | Type::List(_) => false,
        }
    }

    fn fmt_type(ty: &Type) -> String {
        match ty {
            Type::Int => "i64".to_string(),
            Type::Float => "f64".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Str => "String".to_string(),
            Type::Void => "()".to_string(),
            Type::List(inner) => format!("Vec<{}>", Self::fmt_type(inner)),
            Type::Named(name) => name.clone(),
        }
    }

    fn fmt_param_type(&self, p: &Param) -> String {
        match p.meta.get("rust.pass").map(|s| s.as_str()) {
            Some("slice") => {
                if let Type::List(inner) = &p.ty {
                    return format!("&[{}]", Self::fmt_type(inner));
                }
            }
            Some("ref") => match &p.ty {
                Type::Str => return "&str".to_string(),
                Type::Named(name) if !self.enum_names.contains(name) => {
                    return format!("&{}", name);
                }
                _ => {}
            },
            _ => {}
        }
        Self::fmt_type(&p.ty)
    }

    fn fmt_struct(&self, s: &StructDecl, out: &mut String) {
        for c in &s.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str("#[derive(Debug, Clone, PartialEq)]\n");
        let vis = if s.meta.get("rust.pub").map(|v| v.as_str()) == Some("false") {
            ""
        } else {
            "pub "
        };
        out.push_str(&format!("{}struct {} {{\n", vis, s.name));
        for f in &s.fields {
            out.push_str(&format!("    pub {}: {},\n", f.name, Self::fmt_type(&f.ty)));
        }
        out.push_str("}\n");
    }

    fn fmt_enum(&self, e: &EnumDecl, out: &mut String) {
        for c in &e.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str("#[derive(Debug, Clone, Copy, PartialEq, Eq)]\n");
        let vis = if e.meta.get("rust.pub").map(|v| v.as_str()) == Some("false") {
            ""
        } else {
            "pub "
        };
        out.push_str(&format!("{}enum {} {{\n", vis, e.name));
        for v in &e.variants {
            out.push_str(&format!("    {},\n", v));
        }
        out.push_str("}\n");
    }

    fn fmt_fn(&mut self, f: &FnDecl, out: &mut String) {
        for c in &f.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        self.borrowed_locals.clear();
        for p in &f.params {
            self.local_env.insert(p.name.clone(), p.ty.clone());
            if matches!(
                p.meta.get("rust.pass").map(|s| s.as_str()),
                Some("slice") | Some("ref")
            ) {
                self.borrowed_locals.insert(p.name.clone());
            }
        }

        let vis = if f.name == "main" || f.meta.get("rust.pub").map(|v| v.as_str()) == Some("false")
        {
            ""
        } else {
            "pub "
        };

        let params_str: Vec<String> = f
            .params
            .iter()
            .map(|p| format!("{}: {}", p.name, self.fmt_param_type(p)))
            .collect();

        if f.ret_ty == Type::Void {
            out.push_str(&format!("{}fn {}({}) {{\n", vis, f.name, params_str.join(", ")));
        } else {
            out.push_str(&format!(
                "{}fn {}({}) -> {} {{\n",
                vis,
                f.name,
                params_str.join(", "),
                Self::fmt_type(&f.ret_ty)
            ));
        }

        for stmt in &f.body {
            self.fmt_stmt(stmt, 1, out);
        }
        out.push_str("}\n");
    }

    fn fmt_test(&mut self, t: &TestDecl, out: &mut String) {
        for c in &t.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        self.borrowed_locals.clear();
        out.push_str(&format!("#[test]\nfn test_{}() {{\n", t.name));
        for stmt in &t.body {
            self.fmt_stmt(stmt, 1, out);
        }
        out.push_str("}\n");
    }

    fn fmt_pat(&self, pat: &MatchPat) -> String {
        match pat {
            MatchPat::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
            MatchPat::Int(v) => v.to_string(),
            MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
            MatchPat::Wildcard => "_".to_string(),
        }
    }

    fn fmt_stmt(&mut self, stmt: &Stmt, indent: usize, out: &mut String) {
        let pad = "    ".repeat(indent);
        match stmt {
            Stmt::Comment { text, .. } => {
                out.push_str(&format!("{}// {}\n", pad, text));
            }
            Stmt::Let {
                name,
                mutable,
                ty,
                value,
                ..
            } => {
                let mut_kw = if *mutable { "mut " } else { "" };
                let val_str = match (ty, value) {
                    (Some(Type::List(_)), Expr::List(items)) if items.is_empty() => {
                        "Vec::new()".to_string()
                    }
                    _ => self.fmt_owned_expr(value),
                };
                if let Some(t) = ty {
                    self.local_env.insert(name.clone(), t.clone());
                    out.push_str(&format!(
                        "{}let {}{}: {} = {};\n",
                        pad,
                        mut_kw,
                        name,
                        Self::fmt_type(t),
                        val_str
                    ));
                } else {
                    if let Some(inferred) = self.expr_ty(value) {
                        self.local_env.insert(name.clone(), inferred);
                    }
                    out.push_str(&format!("{}let {}{} = {};\n", pad, mut_kw, name, val_str));
                }
                self.borrowed_locals.remove(name);
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
                        let idx_str = match index {
                            Expr::Binary { .. } | Expr::Unary { .. } => {
                                format!("({}) as usize", self.fmt_expr(index))
                            }
                            _ => format!("{} as usize", self.fmt_expr(index)),
                        };
                        format!("{}[{}]", base, idx_str)
                    }
                };
                let rhs_str = if *op == AssignOp::AddAssign
                    && (self.target_ty(target) == Some(Type::Str)
                        || self.expr_ty(value) == Some(Type::Str))
                {
                    match value {
                        Expr::Str(s) => format!("\"{}\"", escape_str(s)),
                        Expr::Var(v) if self.borrowed_locals.contains(v) => v.clone(),
                        _ => format!("&{}", self.fmt_expr(value)),
                    }
                } else {
                    self.fmt_owned_expr(value)
                };
                out.push_str(&format!("{}{} {} {};\n", pad, tgt, op_str, rhs_str));
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
                let is_str_match = arms.iter().any(|a| matches!(a.pat, MatchPat::Str(_)));
                let scrutinee = if is_str_match {
                    if let Expr::Var(v) = expr {
                        if self.borrowed_locals.contains(v) {
                            v.clone()
                        } else {
                            format!("{}.as_str()", v)
                        }
                    } else {
                        format!("{}.as_str()", self.fmt_expr_postfix(expr))
                    }
                } else {
                    self.fmt_expr(expr)
                };
                out.push_str(&format!("{}match {} {{\n", pad, scrutinee));
                for arm in arms {
                    out.push_str(&format!("{}    {} => {{\n", pad, self.fmt_pat(&arm.pat)));
                    let saved = self.local_env.clone();
                    for s in &arm.body {
                        self.fmt_stmt(s, indent + 2, out);
                    }
                    self.local_env = saved;
                    out.push_str(&format!("{}    }}\n", pad));
                }
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::While { cond, body, .. } => {
                out.push_str(&format!("{}while {} {{\n", pad, self.fmt_expr(cond)));
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
                let iter_str = self.fmt_expr_postfix(iter);
                out.push_str(&format!(
                    "{}for {} in {}.iter().cloned() {{\n",
                    pad, var, iter_str
                ));
                let saved = self.local_env.clone();
                let saved_borrowed = self.borrowed_locals.clone();
                if let Some(Type::List(elem)) = self.expr_ty(iter) {
                    self.local_env.insert(var.clone(), *elem);
                }
                self.borrowed_locals.remove(var);
                for s in body {
                    self.fmt_stmt(s, indent + 1, out);
                }
                self.local_env = saved;
                self.borrowed_locals = saved_borrowed;
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
                    "{}for {} in {}..{} {{\n",
                    pad,
                    var,
                    self.fmt_expr(start),
                    self.fmt_expr(end)
                ));
                let saved = self.local_env.clone();
                let saved_borrowed = self.borrowed_locals.clone();
                self.local_env.insert(var.clone(), Type::Int);
                self.borrowed_locals.remove(var);
                for s in body {
                    self.fmt_stmt(s, indent + 1, out);
                }
                self.local_env = saved;
                self.borrowed_locals = saved_borrowed;
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::Break { .. } => out.push_str(&format!("{}break;\n", pad)),
            Stmt::Continue { .. } => out.push_str(&format!("{}continue;\n", pad)),
            Stmt::Return { value, .. } => match value {
                Some(Expr::Var(name)) if !self.borrowed_locals.contains(name) => {
                    out.push_str(&format!("{}return {};\n", pad, name));
                }
                Some(v) => out.push_str(&format!("{}return {};\n", pad, self.fmt_owned_expr(v))),
                None => out.push_str(&format!("{}return;\n", pad)),
            },
            Stmt::Assert { cond, .. } => {
                out.push_str(&format!("{}assert!({});\n", pad, self.fmt_expr(cond)));
            }
            Stmt::AssertEq { left, right, .. } => {
                out.push_str(&format!(
                    "{}assert_eq!({}, {});\n",
                    pad,
                    self.fmt_assert_operand(left),
                    self.fmt_assert_operand(right)
                ));
            }
            Stmt::Expr { expr, .. } => {
                out.push_str(&format!("{}{};\n", pad, self.fmt_expr(expr)));
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
        let pad = "    ".repeat(indent);
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

    fn fmt_assert_operand(&self, expr: &Expr) -> String {
        if let Expr::Var(name) = expr {
            if self.borrowed_locals.contains(name) {
                return self.fmt_owned_expr(expr);
            }
        }
        self.fmt_expr(expr)
    }

    fn fmt_owned_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Var(name) if self.borrowed_locals.contains(name) => {
                if matches!(self.local_env.get(name), Some(Type::Str)) {
                    return format!("{}.to_string()", name);
                }
                format!("{}.to_vec()", name)
            }
            Expr::Var(name) => {
                if let Some(ty) = self.local_env.get(name) {
                    if !self.is_copy_ty(ty) {
                        return format!("{}.clone()", name);
                    }
                }
                name.clone()
            }
            Expr::FieldAccess { .. } | Expr::Index { .. } => {
                let s = self.fmt_expr(expr);
                if let Some(ty) = self.expr_ty(expr) {
                    if !self.is_copy_ty(&ty) {
                        return format!("{}.clone()", s);
                    }
                }
                s
            }
            _ => self.fmt_expr(expr),
        }
    }

    fn fmt_expr_postfix(&self, expr: &Expr) -> String {
        let s = self.fmt_expr(expr);
        match expr {
            Expr::Binary { .. } | Expr::Unary { .. } => format!("({})", s),
            Expr::Int(v) if *v < 0 => format!("({})", s),
            Expr::Float(v) if *v < 0.0 => format!("({})", s),
            Expr::Intrinsic(intr) if matches!(intr.as_ref(), Intrinsic::Len(_)) => {
                format!("({})", s)
            }
            _ => s,
        }
    }

    fn fmt_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => v.to_string(),
            Expr::Float(v) => format_float(*v),
            Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Expr::Str(s) => format!("\"{}\".to_string()", escape_str(s)),
            Expr::Var(v) => v.clone(),
            Expr::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
            Expr::List(items) => {
                if items.is_empty() {
                    "Vec::new()".to_string()
                } else {
                    let inner: Vec<String> =
                        items.iter().map(|e| self.fmt_owned_expr(e)).collect();
                    format!("vec![{}]", inner.join(", "))
                }
            }
            Expr::StructInit { name, fields } => {
                let inner: Vec<String> = fields
                    .iter()
                    .map(|(fname, fval)| format!("{}: {}", fname, self.fmt_owned_expr(fval)))
                    .collect();
                format!("{} {{ {} }}", name, inner.join(", "))
            }
            Expr::FieldAccess { base, field } => {
                format!("{}.{}", self.fmt_expr_postfix(base), field)
            }
            Expr::Index { base, index } => {
                let idx_str = match index.as_ref() {
                    Expr::Binary { .. } | Expr::Unary { .. } => {
                        format!("({}) as usize", self.fmt_expr(index))
                    }
                    _ => format!("{} as usize", self.fmt_expr(index)),
                };
                format!("{}[{}]", self.fmt_expr_postfix(base), idx_str)
            }
            Expr::Unary { op, expr: inner } => {
                let sym = match op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "!",
                };
                match inner.as_ref() {
                    Expr::Binary { .. } | Expr::Unary { .. } => {
                        format!("{}({})", sym, self.fmt_expr(inner))
                    }
                    Expr::Intrinsic(intr) if matches!(intr.as_ref(), Intrinsic::Len(_)) => {
                        format!("{}({})", sym, self.fmt_expr(inner))
                    }
                    _ => format!("{}{}", sym, self.fmt_expr(inner)),
                }
            }
            Expr::Binary { op, left, right } => {
                if *op == BinOp::Add
                    && (self.expr_ty(left) == Some(Type::Str)
                        || self.expr_ty(right) == Some(Type::Str))
                {
                    return format!(
                        "format!(\"{{}}{{}}\", {}, {})",
                        self.fmt_expr(left),
                        self.fmt_expr(right)
                    );
                }
                let l_str = if needs_parens(left, *op, false) {
                    format!("({})", self.fmt_expr(left))
                } else {
                    self.fmt_expr(left)
                };
                let r_str = if needs_parens(right, *op, true) {
                    format!("({})", self.fmt_expr(right))
                } else {
                    self.fmt_expr(right)
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
                format!("{} {} {}", l_str, op_str, r_str)
            }
            Expr::Call { func, args } => {
                let sig = self.fn_sigs.get(func);
                let formatted_args: Vec<String> = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        let pass = sig
                            .and_then(|(ps, _)| ps.get(i))
                            .and_then(|(_, m)| m.as_deref());
                        match pass {
                            Some("slice") | Some("ref") => match arg {
                                Expr::Var(v) if self.borrowed_locals.contains(v) => v.clone(),
                                Expr::Str(s) if pass == Some("ref") => {
                                    format!("\"{}\"", escape_str(s))
                                }
                                Expr::Binary { .. }
                                | Expr::Unary { .. }
                                | Expr::Intrinsic(_) => format!("&({})", self.fmt_expr(arg)),
                                _ => format!("&{}", self.fmt_expr(arg)),
                            },
                            _ => self.fmt_owned_expr(arg),
                        }
                    })
                    .collect();
                format!("{}({})", func, formatted_args.join(", "))
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e) => format!("{}.len() as i64", self.fmt_expr_postfix(e)),
                Intrinsic::Min(a, b) => {
                    format!("{}.min({})", self.fmt_expr_postfix(a), self.fmt_expr(b))
                }
                Intrinsic::Max(a, b) => {
                    format!("{}.max({})", self.fmt_expr_postfix(a), self.fmt_expr(b))
                }
                Intrinsic::Abs(a) => format!("{}.abs()", self.fmt_expr_postfix(a)),
                Intrinsic::Push { list, value } => {
                    format!(
                        "{}.push({})",
                        self.fmt_expr_postfix(list),
                        self.fmt_owned_expr(value)
                    )
                }
                Intrinsic::Print(args) => {
                    if args.is_empty() {
                        "println!()".to_string()
                    } else if args.len() == 1 {
                        if let Expr::Str(s) = &args[0] {
                            return format!("println!(\"{}\")", escape_str(s));
                        }
                        let placeholder = match self.expr_ty(&args[0]) {
                            Some(Type::List(_)) => "{:?}",
                            Some(Type::Named(_)) => "{:?}",
                            _ => "{}",
                        };
                        format!("println!(\"{}\", {})", placeholder, self.fmt_expr(&args[0]))
                    } else {
                        let mut placeholders = Vec::new();
                        let mut rendered_args = Vec::new();
                        for a in args {
                            let ph = match self.expr_ty(a) {
                                Some(Type::List(_)) | Some(Type::Named(_)) => "{:?}",
                                _ => "{}",
                            };
                            placeholders.push(ph);
                            if let Expr::Str(s) = a {
                                rendered_args.push(format!("\"{}\"", escape_str(s)));
                            } else {
                                rendered_args.push(self.fmt_expr(a));
                            }
                        }
                        format!(
                            "println!(\"{}\", {})",
                            placeholders.join(" "),
                            rendered_args.join(", ")
                        )
                    }
                }
                Intrinsic::Contains { haystack, needle } => {
                    let needle_str = match needle {
                        Expr::Str(s) => format!("\"{}\"", escape_str(s)),
                        _ => format!("&{}", self.fmt_expr(needle)),
                    };
                    format!(
                        "{}.contains({})",
                        self.fmt_expr_postfix(haystack),
                        needle_str
                    )
                }
                Intrinsic::Upper(e) => format!("{}.to_uppercase()", self.fmt_expr_postfix(e)),
                Intrinsic::Lower(e) => format!("{}.to_lowercase()", self.fmt_expr_postfix(e)),
                Intrinsic::ToStr(e) => format!("format!(\"{{}}\", {})", self.fmt_expr(e)),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum RTokKind {
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
    ColonColon,
    Dot,
    DotDot,
    Arrow,
    FatArrow,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
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
    Hash,
}

#[derive(Debug, Clone)]
struct RTok {
    kind: RTokKind,
    line: usize,
    col: usize,
}

fn lex_rust(src: &str) -> Result<Vec<RTok>, Diagnostic> {
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
            let start_col = col;
            i += 2;
            col += 2;
            if i < chars.len() && chars[i] == '/' {
                i += 1;
                col += 1;
            }
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
            tokens.push(RTok {
                kind: RTokKind::Comment(text),
                line,
                col: start_col,
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
                    "rust",
                    "unterminated string literal",
                    s_line,
                    s_col,
                ));
            }
            tokens.push(RTok {
                kind: RTokKind::Str(unescape_string(&raw)),
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
            if i + 1 < chars.len()
                && chars[i] == '.'
                && chars[i + 1] != '.'
                && chars[i + 1].is_ascii_digit()
            {
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
                    .map_err(|_| Diagnostic::new("rust", "invalid float literal", line, s_col))?;
                tokens.push(RTok {
                    kind: RTokKind::Float(v),
                    line,
                    col: s_col,
                });
            } else {
                let v = num_str.parse::<i64>().map_err(|_| {
                    Diagnostic::new("rust", "invalid integer literal", line, s_col)
                })?;
                tokens.push(RTok {
                    kind: RTokKind::Int(v),
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
            tokens.push(RTok {
                kind: RTokKind::Ident(ident),
                line,
                col: s_col,
            });
            continue;
        }

        let s_col = col;
        if i + 1 < chars.len() {
            let tok2 = match (chars[i], chars[i + 1]) {
                (':', ':') => Some(RTokKind::ColonColon),
                ('.', '.') => Some(RTokKind::DotDot),
                ('-', '>') => Some(RTokKind::Arrow),
                ('=', '>') => Some(RTokKind::FatArrow),
                ('&', '&') => Some(RTokKind::AmpAmp),
                ('|', '|') => Some(RTokKind::PipePipe),
                ('=', '=') => Some(RTokKind::EqEq),
                ('!', '=') => Some(RTokKind::BangEq),
                ('<', '=') => Some(RTokKind::Le),
                ('>', '=') => Some(RTokKind::Ge),
                ('+', '=') => Some(RTokKind::PlusEq),
                ('-', '=') => Some(RTokKind::MinusEq),
                _ => None,
            };
            if let Some(kind) = tok2 {
                tokens.push(RTok {
                    kind,
                    line,
                    col: s_col,
                });
                i += 2;
                col += 2;
                continue;
            }
        }

        let tok1 = match ch {
            '(' => RTokKind::LParen,
            ')' => RTokKind::RParen,
            '{' => RTokKind::LBrace,
            '}' => RTokKind::RBrace,
            '[' => RTokKind::LBracket,
            ']' => RTokKind::RBracket,
            ',' => RTokKind::Comma,
            ';' => RTokKind::Semi,
            ':' => RTokKind::Colon,
            '.' => RTokKind::Dot,
            '+' => RTokKind::Plus,
            '-' => RTokKind::Minus,
            '*' => RTokKind::Star,
            '/' => RTokKind::Slash,
            '%' => RTokKind::Percent,
            '&' => RTokKind::Amp,
            '!' => RTokKind::Bang,
            '=' => RTokKind::Eq,
            '<' => RTokKind::Lt,
            '>' => RTokKind::Gt,
            '#' => RTokKind::Hash,
            other => {
                return Err(Diagnostic::new(
                    "rust",
                    format!("unexpected character '{}'", other),
                    line,
                    s_col,
                ))
            }
        };
        tokens.push(RTok {
            kind: tok1,
            line,
            col: s_col,
        });
        i += 1;
        col += 1;
    }

    Ok(tokens)
}

struct RustParser {
    tokens: Vec<RTok>,
    pos: usize,
    allow_struct_lit: bool,
}

impl RustParser {
    fn peek(&self) -> Option<&RTok> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&RTokKind> {
        self.peek().map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<RTok> {
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
        Err(Diagnostic::new("rust", msg, line, col))
    }

    fn eat(&mut self, expected: &RTokKind) -> bool {
        if self.peek_kind() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if matches!(self.peek_kind(), Some(RTokKind::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &RTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(expected) {
            Ok(())
        } else {
            self.err(format!("expected {}", label))
        }
    }

    fn expect_ident(&mut self) -> Result<String, Diagnostic> {
        match self.next() {
            Some(RTok {
                kind: RTokKind::Ident(s),
                ..
            }) => Ok(s),
            _ => self.err("expected identifier"),
        }
    }

    fn parse_attributes(&mut self) -> Result<bool, Diagnostic> {
        let mut is_test = false;
        while self.eat(&RTokKind::Hash) {
            self.expect(&RTokKind::LBracket, "'[' after '#'")?;
            let mut depth = 1;
            while depth > 0 {
                match self.next() {
                    Some(RTok {
                        kind: RTokKind::LBracket,
                        ..
                    }) => depth += 1,
                    Some(RTok {
                        kind: RTokKind::RBracket,
                        ..
                    }) => depth -= 1,
                    Some(RTok {
                        kind: RTokKind::Ident(s),
                        ..
                    }) if depth == 1 && s == "test" => {
                        is_test = true;
                    }
                    Some(_) => {}
                    None => return self.err("unterminated attribute '#[...]'"),
                }
            }
        }
        Ok(is_test)
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut module = HubModule::new();
        let mut comments = Vec::new();
        let mut pending_test_attr = false;

        while self.peek().is_some() {
            if let Some(RTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.next();
                comments.push(c);
                continue;
            }
            if self.parse_attributes()? {
                pending_test_attr = true;
            }
            if let Some(RTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.next();
                comments.push(c);
                continue;
            }
            if self.peek().is_none() {
                break;
            }

            let is_pub = self.eat_kw("pub");
            let item_comments = std::mem::take(&mut comments);
            let is_test = std::mem::replace(&mut pending_test_attr, false);

            if self.eat_kw("struct") {
                let s = self.parse_struct(is_pub, item_comments)?;
                module.items.push(Item::Struct(s));
            } else if self.eat_kw("enum") {
                let e = self.parse_enum(is_pub, item_comments)?;
                module.items.push(Item::Enum(e));
            } else if self.eat_kw("fn") {
                let f = self.parse_fn(is_pub, item_comments)?;
                if is_test
                    || (f.params.is_empty()
                        && f.ret_ty == Type::Void
                        && f.name.starts_with("test_")
                        && f.name.len() > 5)
                {
                    let canon = f
                        .name
                        .strip_prefix("test_")
                        .filter(|s| !s.is_empty())
                        .unwrap_or(&f.name)
                        .to_string();
                    module.items.push(Item::Test(TestDecl {
                        id: 0,
                        name: canon,
                        body: f.body,
                        comments: f.comments,
                        meta: Metadata::new(),
                    }));
                } else {
                    module.items.push(Item::Function(f));
                }
            } else {
                return self.err("expected 'struct', 'enum', or 'fn' at top level");
            }
        }

        Ok(module)
    }

    fn parse_struct(
        &mut self,
        is_pub: bool,
        comments: Vec<String>,
    ) -> Result<StructDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&RTokKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), Some(RTokKind::RBrace) | None) {
            if let Some(RTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            let _ = self.eat_kw("pub");
            let fname = self.expect_ident()?;
            self.expect(&RTokKind::Colon, "':'")?;
            let (fty, _) = self.parse_type()?;
            let _ = self.eat(&RTokKind::Comma);
            fields.push(Field {
                id: 0,
                name: fname,
                ty: fty,
                meta: Metadata::new(),
            });
        }
        self.expect(&RTokKind::RBrace, "'}'")?;
        let mut meta = Metadata::new();
        if !is_pub {
            meta.insert("rust.pub".to_string(), "false".to_string());
        }
        Ok(StructDecl {
            id: 0,
            name,
            fields,
            comments,
            meta,
        })
    }

    fn parse_enum(&mut self, is_pub: bool, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&RTokKind::LBrace, "'{'")?;
        let mut variants = Vec::new();
        while !matches!(self.peek_kind(), Some(RTokKind::RBrace) | None) {
            if let Some(RTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            variants.push(self.expect_ident()?);
            let _ = self.eat(&RTokKind::Comma);
        }
        self.expect(&RTokKind::RBrace, "'}'")?;
        let mut meta = Metadata::new();
        if !is_pub {
            meta.insert("rust.pub".to_string(), "false".to_string());
        }
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta,
        })
    }

    fn parse_fn(&mut self, is_pub: bool, comments: Vec<String>) -> Result<FnDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&RTokKind::LParen, "'('")?;
        let mut params = Vec::new();
        while !matches!(self.peek_kind(), Some(RTokKind::RParen) | None) {
            let _ = self.eat_kw("mut");
            let pname = self.expect_ident()?;
            self.expect(&RTokKind::Colon, "':'")?;
            let (pty, pass_meta) = self.parse_type()?;
            let mut pmeta = Metadata::new();
            if let Some(pass) = pass_meta {
                pmeta.insert("rust.pass".to_string(), pass);
            }
            params.push(Param {
                id: 0,
                name: pname,
                ty: pty,
                meta: pmeta,
            });
            if !self.eat(&RTokKind::Comma) {
                break;
            }
        }
        self.expect(&RTokKind::RParen, "')'")?;

        let ret_ty = if self.eat(&RTokKind::Arrow) {
            let (t, _) = self.parse_type()?;
            t
        } else {
            Type::Void
        };

        let body = self.parse_block(ret_ty != Type::Void)?;
        let mut meta = Metadata::new();
        if name != "main" && !is_pub {
            meta.insert("rust.pub".to_string(), "false".to_string());
        }

        Ok(FnDecl {
            id: 0,
            name,
            params,
            ret_ty,
            body,
            comments,
            meta,
        })
    }

    fn parse_type(&mut self) -> Result<(Type, Option<String>), Diagnostic> {
        if self.eat(&RTokKind::LParen) {
            self.expect(&RTokKind::RParen, "')'")?;
            return Ok((Type::Void, None));
        }
        if self.eat(&RTokKind::Amp) {
            let _ = self.eat_kw("mut");
            if self.eat(&RTokKind::LBracket) {
                let (inner, _) = self.parse_type()?;
                self.expect(&RTokKind::RBracket, "']'")?;
                return Ok((Type::list(inner), Some("slice".to_string())));
            }
            let ident = self.expect_ident()?;
            return match ident.as_str() {
                "str" | "String" => Ok((Type::Str, Some("ref".to_string()))),
                other => Ok((Type::Named(other.to_string()), Some("ref".to_string()))),
            };
        }

        let ident = self.expect_ident()?;
        match ident.as_str() {
            "i64" | "i32" | "isize" | "usize" => Ok((Type::Int, None)),
            "f64" | "f32" => Ok((Type::Float, None)),
            "bool" => Ok((Type::Bool, None)),
            "String" => Ok((Type::Str, None)),
            "Vec" => {
                self.expect(&RTokKind::Lt, "'<' after Vec")?;
                let (inner, _) = self.parse_type()?;
                self.expect(&RTokKind::Gt, "'>' after Vec<T")?;
                Ok((Type::list(inner), None))
            }
            other => Ok((Type::Named(other.to_string()), None)),
        }
    }

    fn parse_block(&mut self, tail_expr_is_return: bool) -> Result<Vec<Stmt>, Diagnostic> {
        self.expect(&RTokKind::LBrace, "'{'")?;
        let mut stmts = Vec::new();
        while !matches!(self.peek_kind(), Some(RTokKind::RBrace) | None) {
            if let Some(RTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.next();
                stmts.push(Stmt::Comment { id: 0, text: c });
                continue;
            }
            if self.eat(&RTokKind::Semi) {
                continue;
            }
            if self.eat_kw("let") {
                let mutable = self.eat_kw("mut");
                let name = self.expect_ident()?;
                let ty = if self.eat(&RTokKind::Colon) {
                    Some(self.parse_type()?.0)
                } else {
                    None
                };
                self.expect(&RTokKind::Eq, "'=' in let binding")?;
                let value = self.parse_expr()?;
                self.expect(&RTokKind::Semi, "';' after let binding")?;
                let mut meta = Metadata::new();
                if mutable {
                    meta.insert("explicit_mut".to_string(), "true".to_string());
                }
                stmts.push(Stmt::Let {
                    id: 0,
                    name,
                    mutable,
                    ty,
                    value,
                    meta,
                });
                continue;
            }
            if self.eat_kw("if") {
                stmts.push(self.parse_if()?);
                continue;
            }
            if self.eat_kw("match") {
                stmts.push(self.parse_match()?);
                continue;
            }
            if self.eat_kw("while") {
                let cond = self.parse_header_expr()?;
                let body = self.parse_block(false)?;
                stmts.push(Stmt::While {
                    id: 0,
                    cond,
                    body,
                    meta: Metadata::new(),
                });
                continue;
            }
            if self.eat_kw("for") {
                let _ = self.eat(&RTokKind::Amp);
                let _ = self.eat_kw("mut");
                let var = self.expect_ident()?;
                if !self.eat_kw("in") {
                    return self.err("expected 'in' inside 'for' loop");
                }
                let first = self.parse_header_expr()?;
                if self.eat(&RTokKind::DotDot) {
                    let end = self.parse_header_expr()?;
                    let body = self.parse_block(false)?;
                    stmts.push(Stmt::ForRange {
                        id: 0,
                        var,
                        start: first,
                        end,
                        body,
                        meta: Metadata::new(),
                    });
                } else {
                    let body = self.parse_block(false)?;
                    stmts.push(Stmt::ForEach {
                        id: 0,
                        var,
                        iter: first,
                        body,
                        meta: Metadata::new(),
                    });
                }
                continue;
            }
            if self.eat_kw("break") {
                let _ = self.eat(&RTokKind::Semi);
                stmts.push(Stmt::Break { id: 0 });
                continue;
            }
            if self.eat_kw("continue") {
                let _ = self.eat(&RTokKind::Semi);
                stmts.push(Stmt::Continue { id: 0 });
                continue;
            }
            if self.eat_kw("return") {
                if self.eat(&RTokKind::Semi) || matches!(self.peek_kind(), Some(RTokKind::RBrace)) {
                    stmts.push(Stmt::Return {
                        id: 0,
                        value: None,
                        meta: Metadata::new(),
                    });
                } else {
                    let val = self.parse_expr()?;
                    let _ = self.eat(&RTokKind::Semi);
                    stmts.push(Stmt::Return {
                        id: 0,
                        value: Some(val),
                        meta: Metadata::new(),
                    });
                }
                continue;
            }

            if matches!(
                self.peek_kind(),
                Some(RTokKind::Ident(s)) if s == "assert" || s == "assert_eq"
            ) && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&RTokKind::Bang)
            {
                let mname = self.expect_ident()?;
                self.expect(&RTokKind::Bang, "'!'")?;
                self.expect(&RTokKind::LParen, "'(' after assert macro")?;
                let mut args = self.parse_arg_list(&RTokKind::RParen)?;
                let _ = self.eat(&RTokKind::Semi);
                if mname == "assert" {
                    if args.is_empty() {
                        return self.err("assert!(...) requires a condition");
                    }
                    let cond = args.remove(0);
                    stmts.push(Stmt::Assert {
                        id: 0,
                        cond,
                        meta: Metadata::new(),
                    });
                } else {
                    if args.len() < 2 {
                        return self.err("assert_eq!(...) requires two arguments");
                    }
                    let left = args.remove(0);
                    let right = args.remove(0);
                    stmts.push(Stmt::AssertEq {
                        id: 0,
                        left,
                        right,
                        meta: Metadata::new(),
                    });
                }
                continue;
            }

            let expr = self.parse_expr()?;
            if let Some(op) = match self.peek_kind() {
                Some(RTokKind::Eq) => Some(AssignOp::Set),
                Some(RTokKind::PlusEq) => Some(AssignOp::AddAssign),
                Some(RTokKind::MinusEq) => Some(AssignOp::SubAssign),
                _ => None,
            } {
                self.next();
                let target = expr_to_assign_target(expr)?;
                let value = self.parse_expr()?;
                self.expect(&RTokKind::Semi, "';' after assignment")?;
                stmts.push(Stmt::Assign {
                    id: 0,
                    target,
                    op,
                    value,
                    meta: Metadata::new(),
                });
            } else if self.eat(&RTokKind::Semi) {
                stmts.push(Stmt::Expr {
                    id: 0,
                    expr,
                    meta: Metadata::new(),
                });
            } else if matches!(self.peek_kind(), Some(RTokKind::RBrace)) && tail_expr_is_return {
                stmts.push(Stmt::Return {
                    id: 0,
                    value: Some(expr),
                    meta: Metadata::new(),
                });
            } else {
                return self.err("expected ';' after expression");
            }
        }
        self.expect(&RTokKind::RBrace, "'}'")?;
        Ok(stmts)
    }

    fn parse_if(&mut self) -> Result<Stmt, Diagnostic> {
        let cond = self.parse_header_expr()?;
        let then_body = self.parse_block(false)?;
        let else_body = if self.eat_kw("else") {
            if self.eat_kw("if") {
                vec![self.parse_if()?]
            } else {
                self.parse_block(false)?
            }
        } else {
            Vec::new()
        };
        Ok(Stmt::If {
            id: 0,
            cond,
            then_body,
            else_body,
            meta: Metadata::new(),
        })
    }

    fn parse_match(&mut self) -> Result<Stmt, Diagnostic> {
        let expr = self.parse_header_expr()?;
        self.expect(&RTokKind::LBrace, "'{' after match scrutinee")?;
        let mut arms = Vec::new();
        while !matches!(self.peek_kind(), Some(RTokKind::RBrace) | None) {
            let pat = self.parse_match_pat()?;
            self.expect(&RTokKind::FatArrow, "'=>' in match arm")?;
            let body = if matches!(self.peek_kind(), Some(RTokKind::LBrace)) {
                self.parse_block(false)?
            } else {
                let single = self.parse_expr()?;
                vec![Stmt::Expr {
                    id: 0,
                    expr: single,
                    meta: Metadata::new(),
                }]
            };
            let _ = self.eat(&RTokKind::Comma);
            arms.push(MatchArm { pat, body });
        }
        self.expect(&RTokKind::RBrace, "'}' after match")?;
        Ok(Stmt::Match {
            id: 0,
            expr,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_match_pat(&mut self) -> Result<MatchPat, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(RTokKind::Ident(s)) if s == "_" => {
                self.next();
                Ok(MatchPat::Wildcard)
            }
            Some(RTokKind::Ident(ename)) => {
                self.next();
                self.expect(&RTokKind::ColonColon, "'::' in enum match pattern")?;
                let variant = self.expect_ident()?;
                Ok(MatchPat::EnumVariant { enum_name: ename, variant })
            }
            Some(RTokKind::Int(v)) => {
                self.next();
                Ok(MatchPat::Int(v))
            }
            Some(RTokKind::Minus) => {
                self.next();
                if let Some(RTokKind::Int(v)) = self.peek_kind().cloned() {
                    self.next();
                    Ok(MatchPat::Int(-v))
                } else {
                    self.err("expected integer after '-' in match pattern")
                }
            }
            Some(RTokKind::Str(s)) => {
                self.next();
                Ok(MatchPat::Str(s))
            }
            _ => self.err("expected match pattern ('_', Enum::Variant, integer, or string)"),
        }
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
        while self.eat(&RTokKind::PipePipe) {
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
        while self.eat(&RTokKind::AmpAmp) {
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
                Some(RTokKind::EqEq) => Some(BinOp::Eq),
                Some(RTokKind::BangEq) => Some(BinOp::Ne),
                Some(RTokKind::Lt) => Some(BinOp::Lt),
                Some(RTokKind::Le) => Some(BinOp::Le),
                Some(RTokKind::Gt) => Some(BinOp::Gt),
                Some(RTokKind::Ge) => Some(BinOp::Ge),
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
                Some(RTokKind::Plus) => Some(BinOp::Add),
                Some(RTokKind::Minus) => Some(BinOp::Sub),
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
        let mut left = self.parse_cast()?;
        loop {
            let op = match self.peek_kind() {
                Some(RTokKind::Star) => Some(BinOp::Mul),
                Some(RTokKind::Slash) => Some(BinOp::Div),
                Some(RTokKind::Percent) => Some(BinOp::Mod),
                _ => None,
            };
            if let Some(op) = op {
                self.next();
                let right = self.parse_cast()?;
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

    fn parse_cast(&mut self) -> Result<Expr, Diagnostic> {
        let expr = self.parse_unary()?;
        while self.eat_kw("as") {
            let _ = self.parse_type()?;
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<Expr, Diagnostic> {
        if self.eat(&RTokKind::Amp) {
            let _ = self.eat_kw("mut");
            return self.parse_unary();
        }
        if self.eat(&RTokKind::Star) {
            return self.parse_unary();
        }
        if self.eat(&RTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        if self.eat(&RTokKind::Bang) {
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
            if self.eat(&RTokKind::Dot) {
                let member = self.expect_ident()?;
                if self.eat(&RTokKind::LParen) {
                    let args = self.parse_arg_list(&RTokKind::RParen)?;
                    base = match (member.as_str(), args.len()) {
                        (
                            "to_string" | "clone" | "to_vec" | "iter" | "copied" | "cloned"
                            | "as_str",
                            0,
                        ) => base,
                        ("len", 0) => Expr::intrinsic(Intrinsic::Len(base)),
                        ("abs", 0) => Expr::intrinsic(Intrinsic::Abs(base)),
                        ("to_uppercase", 0) => Expr::intrinsic(Intrinsic::Upper(base)),
                        ("to_lowercase", 0) => Expr::intrinsic(Intrinsic::Lower(base)),
                        ("min", 1) => {
                            Expr::intrinsic(Intrinsic::Min(base, args.into_iter().next().unwrap()))
                        }
                        ("max", 1) => {
                            Expr::intrinsic(Intrinsic::Max(base, args.into_iter().next().unwrap()))
                        }
                        ("push", 1) => Expr::intrinsic(Intrinsic::Push {
                            list: base,
                            value: args.into_iter().next().unwrap(),
                        }),
                        ("contains", 1) => Expr::intrinsic(Intrinsic::Contains {
                            haystack: base,
                            needle: args.into_iter().next().unwrap(),
                        }),
                        _ => {
                            return self.err(format!(
                                "unsupported method '.{}(...)' in Star subset",
                                member
                            ));
                        }
                    };
                } else {
                    base = Expr::FieldAccess {
                        base: Box::new(base),
                        field: member,
                    };
                }
            } else if self.eat(&RTokKind::LBracket) {
                let prev = self.allow_struct_lit;
                self.allow_struct_lit = true;
                let idx = self.parse_expr()?;
                self.allow_struct_lit = prev;
                self.expect(&RTokKind::RBracket, "']'")?;
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
            Some(RTokKind::Int(v)) => {
                self.next();
                Ok(Expr::Int(v))
            }
            Some(RTokKind::Float(v)) => {
                self.next();
                Ok(Expr::Float(v))
            }
            Some(RTokKind::Str(s)) => {
                self.next();
                Ok(Expr::Str(s))
            }
            Some(RTokKind::LParen) => {
                self.next();
                let prev = self.allow_struct_lit;
                self.allow_struct_lit = true;
                let e = self.parse_expr()?;
                self.allow_struct_lit = prev;
                self.expect(&RTokKind::RParen, "')'")?;
                Ok(e)
            }
            Some(RTokKind::Ident(ident)) => {
                self.next();
                if ident == "true" {
                    return Ok(Expr::Bool(true));
                }
                if ident == "false" {
                    return Ok(Expr::Bool(false));
                }
                if self.eat(&RTokKind::ColonColon) {
                    let member = self.expect_ident()?;
                    if ident == "Vec" && member == "new" {
                        self.expect(&RTokKind::LParen, "'('")?;
                        self.expect(&RTokKind::RParen, "')'")?;
                        return Ok(Expr::List(Vec::new()));
                    }
                    return Ok(Expr::EnumVariant {
                        enum_name: ident,
                        variant: member,
                    });
                }
                if self.eat(&RTokKind::Bang) {
                    match ident.as_str() {
                        "vec" => {
                            self.expect(&RTokKind::LBracket, "'[' after vec!")?;
                            let items = self.parse_arg_list(&RTokKind::RBracket)?;
                            return Ok(Expr::List(items));
                        }
                        "println" => {
                            self.expect(&RTokKind::LParen, "'(' after println!")?;
                            let args = self.parse_arg_list(&RTokKind::RParen)?;
                            return Ok(parse_println_args(args));
                        }
                        "format" => {
                            self.expect(&RTokKind::LParen, "'(' after format!")?;
                            let mut args = self.parse_arg_list(&RTokKind::RParen)?;
                            if args.len() == 2 {
                                if let Expr::Str(fmt) = &args[0] {
                                    if fmt == "{}" {
                                        let inner = args.pop().unwrap();
                                        return Ok(Expr::intrinsic(Intrinsic::ToStr(inner)));
                                    }
                                }
                            }
                            if args.len() == 3 {
                                if let Expr::Str(fmt) = &args[0] {
                                    if fmt == "{}{}" {
                                        let right = args.pop().unwrap();
                                        let left = args.pop().unwrap();
                                        return Ok(Expr::Binary {
                                            op: BinOp::Add,
                                            left: Box::new(left),
                                            right: Box::new(right),
                                        });
                                    }
                                }
                            }
                            return self.err(
                                "only format!(\"{}\", x) and format!(\"{}{}\", a, b) are supported",
                            );
                        }
                        other => return self.err(format!("unsupported macro '{}!'", other)),
                    }
                }
                if self.eat(&RTokKind::LParen) {
                    let args = self.parse_arg_list(&RTokKind::RParen)?;
                    return Ok(Expr::Call { func: ident, args });
                }
                if self.allow_struct_lit
                    && ident
                        .chars()
                        .next()
                        .map(|c| c.is_ascii_uppercase())
                        .unwrap_or(false)
                    && self.eat(&RTokKind::LBrace)
                {
                    let mut fields = Vec::new();
                    while !matches!(self.peek_kind(), Some(RTokKind::RBrace) | None) {
                        let fname = self.expect_ident()?;
                        let fval = if self.eat(&RTokKind::Colon) {
                            let prev = self.allow_struct_lit;
                            self.allow_struct_lit = true;
                            let v = self.parse_expr()?;
                            self.allow_struct_lit = prev;
                            v
                        } else {
                            Expr::Var(fname.clone())
                        };
                        fields.push((fname, fval));
                        if !self.eat(&RTokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&RTokKind::RBrace, "'}' after struct literal")?;
                    return Ok(Expr::StructInit {
                        name: ident,
                        fields,
                    });
                }

                Ok(Expr::Var(ident))
            }
            _ => self.err("expected expression"),
        }
    }

    fn parse_arg_list(&mut self, closing: &RTokKind) -> Result<Vec<Expr>, Diagnostic> {
        let prev = self.allow_struct_lit;
        self.allow_struct_lit = true;
        let mut items = Vec::new();
        while self.peek_kind() != Some(closing) && self.peek().is_some() {
            items.push(self.parse_expr()?);
            if !self.eat(&RTokKind::Comma) {
                break;
            }
        }
        self.allow_struct_lit = prev;
        self.expect(closing, "closing delimiter")?;
        Ok(items)
    }
}

fn parse_println_args(mut args: Vec<Expr>) -> Expr {
    if args.is_empty() {
        return Expr::intrinsic(Intrinsic::Print(Vec::new()));
    }
    if args.len() == 1 {
        return Expr::intrinsic(Intrinsic::Print(args));
    }
    if let Expr::Str(fmt) = &args[0] {
        let tokens: Vec<&str> = fmt.split(' ').collect();
        if tokens.len() == args.len() - 1
            && tokens.iter().all(|t| *t == "{}" || *t == "{:?}")
        {
            args.remove(0);
            return Expr::intrinsic(Intrinsic::Print(args));
        }

        let fmt_owned = fmt.clone();
        let rest: Vec<Expr> = args.into_iter().skip(1).collect();
        let mut out = Vec::new();
        let mut arg_iter = rest.into_iter();
        let mut remainder = fmt_owned.as_str();

        while let Some(pos) = remainder.find('{') {
            let prefix = remainder[..pos].trim();
            if !prefix.is_empty() {
                out.push(Expr::Str(prefix.to_string()));
            }
            if let Some(end_brace) = remainder[pos..].find('}') {
                remainder = &remainder[pos + end_brace + 1..];
                if let Some(a) = arg_iter.next() {
                    out.push(a);
                }
            } else {
                break;
            }
        }
        let tail = remainder.trim();
        if !tail.is_empty() {
            out.push(Expr::Str(tail.to_string()));
        }
        out.extend(arg_iter);
        return Expr::intrinsic(Intrinsic::Print(out));
    }
    Expr::intrinsic(Intrinsic::Print(args))
}

fn expr_to_assign_target(expr: Expr) -> Result<AssignTarget, Diagnostic> {
    match expr {
        Expr::Var(v) => Ok(AssignTarget::Var(v)),
        Expr::FieldAccess { base, field } => {
            if let Expr::Var(b) = *base {
                Ok(AssignTarget::Field { base: b, field })
            } else {
                Err(Diagnostic::new(
                    "rust",
                    "nested field assignment target not supported",
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
                    "rust",
                    "nested index assignment target not supported",
                    1,
                    1,
                ))
            }
        }
        _ => Err(Diagnostic::new("rust", "invalid assignment target", 1, 1)),
    }
}

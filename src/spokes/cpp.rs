use std::collections::{BTreeSet, HashMap, HashSet};

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl,
    HubModule, Intrinsic, Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl,
    Type, UnaryOp,
};
use crate::lens::{binop_prec, escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct CppLens;

impl LanguageLens for CppLens {
    fn id(&self) -> SpokeId {
        SpokeId::Cpp
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut ctx = CppFmtCtx::from_hub(hub);
        let (headers, need_lower, need_upper) = ctx.collect_headers(hub);

        let mut out = String::new();
        for h in &headers {
            out.push_str(&format!("#include <{}>\n", h));
        }

        if need_lower {
            out.push_str(
                "\ninline std::string star_to_lower(std::string s) {\n    for (char& ch : s) ch = static_cast<char>(std::tolower(static_cast<unsigned char>(ch)));\n    return s;\n}\n",
            );
        }
        if need_upper {
            out.push_str(
                "\ninline std::string star_to_upper(std::string s) {\n    for (char& ch : s) ch = static_cast<char>(std::toupper(static_cast<unsigned char>(ch)));\n    return s;\n}\n",
            );
        }

        for item in &hub.items {
            if !out.is_empty() {
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
        let tokens = lex_cpp(source)?;
        let mut known_enums: HashSet<String> = HashSet::new();
        let mut struct_field_order: HashMap<String, Vec<String>> = HashMap::new();
        for item in &prev_hub.items {
            match item {
                Item::Enum(e) => {
                    known_enums.insert(e.name.clone());
                }
                Item::Struct(s) => {
                    struct_field_order
                        .insert(s.name.clone(), s.fields.iter().map(|f| f.name.clone()).collect());
                }
                _ => {}
            }
        }
        let mut parser = CppParser {
            tokens,
            pos: 0,
            known_enums,
            struct_field_order,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Cpp))
    }
}

struct CppFmtCtx {
    fn_ret_types: HashMap<String, Type>,
    struct_fields: HashMap<String, HashMap<String, Type>>,
    enum_names: HashSet<String>,
    local_env: HashMap<String, Type>,
}

impl CppFmtCtx {
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

    fn is_ref_default_ty(&self, ty: &Type) -> bool {
        match ty {
            Type::List(_) | Type::Str => true,
            Type::Named(n) => !self.enum_names.contains(n),
            _ => false,
        }
    }

    fn collect_headers(&mut self, hub: &HubModule) -> (BTreeSet<&'static str>, bool, bool) {
        let mut headers = BTreeSet::new();
        let mut need_lower = false;
        let mut need_upper = false;
        headers.insert("cstdint");

        for item in &hub.items {
            match item {
                Item::Struct(s) => {
                    for f in &s.fields {
                        Self::scan_type_headers(&f.ty, &mut headers);
                    }
                }
                Item::Enum(_) => {}
                Item::Function(f) => {
                    self.local_env.clear();
                    for p in &f.params {
                        Self::scan_type_headers(&p.ty, &mut headers);
                        self.local_env.insert(p.name.clone(), p.ty.clone());
                    }
                    Self::scan_type_headers(&f.ret_ty, &mut headers);
                    self.scan_stmts_headers(
                        &f.body,
                        &mut headers,
                        &mut need_lower,
                        &mut need_upper,
                    );
                }
                Item::Test(t) => {
                    headers.insert("cassert");
                    self.local_env.clear();
                    self.scan_stmts_headers(
                        &t.body,
                        &mut headers,
                        &mut need_lower,
                        &mut need_upper,
                    );
                }
            }
        }
        (headers, need_lower, need_upper)
    }

    fn scan_type_headers(ty: &Type, headers: &mut BTreeSet<&'static str>) {
        match ty {
            Type::Str => {
                headers.insert("string");
            }
            Type::List(inner) => {
                headers.insert("vector");
                Self::scan_type_headers(inner, headers);
            }
            _ => {}
        }
    }

    fn scan_stmts_headers(
        &mut self,
        stmts: &[Stmt],
        headers: &mut BTreeSet<&'static str>,
        need_lower: &mut bool,
        need_upper: &mut bool,
    ) {
        for s in stmts {
            match s {
                Stmt::Let {
                    name, ty, value, ..
                } => {
                    if let Some(t) = ty {
                        Self::scan_type_headers(t, headers);
                    }
                    self.scan_expr_headers(value, headers, need_lower, need_upper);
                    if let Some(t) = ty.clone().or_else(|| self.expr_ty(value)) {
                        self.local_env.insert(name.clone(), t);
                    }
                }
                Stmt::Assign { target, value, .. } => {
                    if let AssignTarget::Index { index, .. } = target {
                        self.scan_expr_headers(index, headers, need_lower, need_upper);
                    }
                    self.scan_expr_headers(value, headers, need_lower, need_upper);
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    self.scan_expr_headers(cond, headers, need_lower, need_upper);
                    let saved = self.local_env.clone();
                    self.scan_stmts_headers(then_body, headers, need_lower, need_upper);
                    self.local_env = saved.clone();
                    self.scan_stmts_headers(else_body, headers, need_lower, need_upper);
                    self.local_env = saved;
                }
                Stmt::Match { expr, arms, .. } => {
                    self.scan_expr_headers(expr, headers, need_lower, need_upper);
                    for arm in arms {
                        if matches!(&arm.pat, MatchPat::Str(_)) {
                            headers.insert("string");
                        }
                        let saved = self.local_env.clone();
                        self.scan_stmts_headers(&arm.body, headers, need_lower, need_upper);
                        self.local_env = saved;
                    }
                }
                Stmt::While { cond, body, .. } => {
                    self.scan_expr_headers(cond, headers, need_lower, need_upper);
                    let saved = self.local_env.clone();
                    self.scan_stmts_headers(body, headers, need_lower, need_upper);
                    self.local_env = saved;
                }
                Stmt::ForEach {
                    var, iter, body, ..
                } => {
                    self.scan_expr_headers(iter, headers, need_lower, need_upper);
                    let saved = self.local_env.clone();
                    if let Some(Type::List(elem)) = self.expr_ty(iter) {
                        self.local_env.insert(var.clone(), *elem);
                    }
                    self.scan_stmts_headers(body, headers, need_lower, need_upper);
                    self.local_env = saved;
                }
                Stmt::ForRange {
                    var,
                    start,
                    end,
                    body,
                    ..
                } => {
                    self.scan_expr_headers(start, headers, need_lower, need_upper);
                    self.scan_expr_headers(end, headers, need_lower, need_upper);
                    let saved = self.local_env.clone();
                    self.local_env.insert(var.clone(), Type::Int);
                    self.scan_stmts_headers(body, headers, need_lower, need_upper);
                    self.local_env = saved;
                }
                Stmt::Assert { cond, .. } => {
                    headers.insert("cassert");
                    self.scan_expr_headers(cond, headers, need_lower, need_upper);
                }
                Stmt::AssertEq { left, right, .. } => {
                    headers.insert("cassert");
                    self.scan_expr_headers(left, headers, need_lower, need_upper);
                    self.scan_expr_headers(right, headers, need_lower, need_upper);
                }
                Stmt::Return {
                    value: Some(e), ..
                }
                | Stmt::Expr { expr: e, .. } => {
                    self.scan_expr_headers(e, headers, need_lower, need_upper);
                }
                _ => {}
            }
        }
    }

    fn scan_expr_headers(
        &self,
        expr: &Expr,
        headers: &mut BTreeSet<&'static str>,
        need_lower: &mut bool,
        need_upper: &mut bool,
    ) {
        match expr {
            Expr::Str(_) => {
                headers.insert("string");
            }
            Expr::List(items) => {
                headers.insert("vector");
                for it in items {
                    self.scan_expr_headers(it, headers, need_lower, need_upper);
                }
            }
            Expr::StructInit { fields, .. } => {
                for (_, v) in fields {
                    self.scan_expr_headers(v, headers, need_lower, need_upper);
                }
            }
            Expr::FieldAccess { base, .. } => {
                self.scan_expr_headers(base, headers, need_lower, need_upper);
            }
            Expr::Index { base, index } => {
                self.scan_expr_headers(base, headers, need_lower, need_upper);
                self.scan_expr_headers(index, headers, need_lower, need_upper);
            }
            Expr::Unary { expr: inner, .. } => {
                self.scan_expr_headers(inner, headers, need_lower, need_upper);
            }
            Expr::Binary { left, right, .. } => {
                self.scan_expr_headers(left, headers, need_lower, need_upper);
                self.scan_expr_headers(right, headers, need_lower, need_upper);
            }
            Expr::Call { args, .. } => {
                for a in args {
                    self.scan_expr_headers(a, headers, need_lower, need_upper);
                }
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Print(args) => {
                    headers.insert("iostream");
                    for a in args {
                        self.scan_expr_headers(a, headers, need_lower, need_upper);
                    }
                }
                Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                    headers.insert("algorithm");
                    self.scan_expr_headers(a, headers, need_lower, need_upper);
                    self.scan_expr_headers(b, headers, need_lower, need_upper);
                }
                Intrinsic::Abs(a) => {
                    headers.insert("cmath");
                    self.scan_expr_headers(a, headers, need_lower, need_upper);
                }
                Intrinsic::ToStr(a) => {
                    headers.insert("string");
                    self.scan_expr_headers(a, headers, need_lower, need_upper);
                }
                Intrinsic::Lower(a) => {
                    headers.insert("string");
                    headers.insert("cctype");
                    *need_lower = true;
                    self.scan_expr_headers(a, headers, need_lower, need_upper);
                }
                Intrinsic::Upper(a) => {
                    headers.insert("string");
                    headers.insert("cctype");
                    *need_upper = true;
                    self.scan_expr_headers(a, headers, need_lower, need_upper);
                }
                Intrinsic::Contains { haystack, needle } => {
                    if matches!(self.expr_ty(haystack), Some(Type::List(_))) {
                        headers.insert("algorithm");
                    } else {
                        headers.insert("string");
                    }
                    self.scan_expr_headers(haystack, headers, need_lower, need_upper);
                    self.scan_expr_headers(needle, headers, need_lower, need_upper);
                }
                Intrinsic::Len(a) => {
                    self.scan_expr_headers(a, headers, need_lower, need_upper);
                }
                Intrinsic::Push { list, value } => {
                    headers.insert("vector");
                    self.scan_expr_headers(list, headers, need_lower, need_upper);
                    self.scan_expr_headers(value, headers, need_lower, need_upper);
                }
            },
            _ => {}
        }
    }

    fn fmt_type(ty: &Type) -> String {
        match ty {
            Type::Int => "int64_t".to_string(),
            Type::Float => "double".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Str => "std::string".to_string(),
            Type::Void => "void".to_string(),
            Type::List(inner) => format!("std::vector<{}>", Self::fmt_type(inner)),
            Type::Named(name) => name.clone(),
        }
    }

    fn fmt_param(&self, p: &Param) -> String {
        let base = Self::fmt_type(&p.ty);
        if self.is_ref_default_ty(&p.ty)
            && p.meta.get("cpp.pass").map(|v| v.as_str()) != Some("value")
        {
            format!("const {}& {}", base, p.name)
        } else {
            format!("{} {}", base, p.name)
        }
    }

    fn fmt_struct(&self, s: &StructDecl, out: &mut String) {
        for c in &s.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("struct {} {{\n", s.name));
        for f in &s.fields {
            out.push_str(&format!("    {} {};\n", Self::fmt_type(&f.ty), f.name));
        }
        let eq_body = if s.fields.is_empty() {
            "true".to_string()
        } else {
            s.fields
                .iter()
                .map(|f| format!("{} == o.{}", f.name, f.name))
                .collect::<Vec<_>>()
                .join(" && ")
        };
        out.push_str(&format!(
            "    bool operator==(const {}& o) const {{ return {}; }}\n",
            s.name, eq_body
        ));
        out.push_str(&format!(
            "    bool operator!=(const {}& o) const {{ return !(*this == o); }}\n",
            s.name
        ));
        out.push_str("};\n");
    }

    fn fmt_enum(&self, e: &EnumDecl, out: &mut String) {
        for c in &e.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("enum class {} : int64_t {{\n", e.name));
        for (idx, v) in e.variants.iter().enumerate() {
            out.push_str(&format!("    {} = {},\n", v, idx));
        }
        out.push_str("};\n");
    }

    fn fmt_fn(&mut self, f: &FnDecl, out: &mut String) {
        for c in &f.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        for p in &f.params {
            self.local_env.insert(p.name.clone(), p.ty.clone());
        }

        let params_str: Vec<String> = f.params.iter().map(|p| self.fmt_param(p)).collect();
        let ret_str = if f.name == "main" && f.ret_ty == Type::Void {
            "int".to_string()
        } else {
            Self::fmt_type(&f.ret_ty)
        };

        out.push_str(&format!("{} {}({}) {{\n", ret_str, f.name, params_str.join(", ")));
        for s in &f.body {
            self.fmt_stmt(s, 1, out);
        }
        if f.name == "main" && f.ret_ty == Type::Void {
            out.push_str("    return 0;\n");
        } else if f.ret_ty != Type::Void && !cpp_block_terminates(&f.body) {
            out.push_str("    __builtin_unreachable();\n");
        }
        out.push_str("}\n");
    }

    fn fmt_test(&mut self, t: &TestDecl, out: &mut String) {
        for c in &t.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        out.push_str(&format!("void test_{}() {{\n", t.name));
        for s in &t.body {
            self.fmt_stmt(s, 1, out);
        }
        out.push_str("}\n");
    }

    fn fmt_pat(&self, pat: &MatchPat) -> String {
        match pat {
            MatchPat::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
            MatchPat::Int(v) => v.to_string(),
            MatchPat::Str(s) => format!("std::string(\"{}\")", escape_str(s)),
            MatchPat::Wildcard => "default".to_string(),
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
                let const_kw = if *mutable { "" } else { "const " };
                if let Some(t) = ty {
                    let val_str = match (t, value) {
                        (Type::List(_), Expr::List(items)) if items.is_empty() => "{}".to_string(),
                        _ => self.fmt_expr(value),
                    };
                    self.local_env.insert(name.clone(), t.clone());
                    out.push_str(&format!(
                        "{}{}{} {} = {};\n",
                        pad,
                        const_kw,
                        Self::fmt_type(t),
                        name,
                        val_str
                    ));
                } else {
                    if let Some(inferred) = self.expr_ty(value) {
                        self.local_env.insert(name.clone(), inferred);
                    }
                    out.push_str(&format!(
                        "{}{}auto {} = {};\n",
                        pad,
                        const_kw,
                        name,
                        self.fmt_expr(value)
                    ));
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
                        format!("{}[{}]", base, self.fmt_clean_int(index))
                    }
                };
                out.push_str(&format!(
                    "{}{} {} {};\n",
                    pad,
                    tgt,
                    op_str,
                    self.fmt_expr(value)
                ));
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
                // C++ switch only supports integral & enum types; string matches lower with `@star-match`
                if self.expr_ty(expr) == Some(Type::Str)
                    || arms.iter().any(|a| matches!(&a.pat, MatchPat::Str(_)))
                {
                    out.push_str(&format!("{}// @star-match\n", pad));
                    let scrut = self.fmt_expr(expr);
                    for (idx, arm) in arms.iter().enumerate() {
                        if arm.pat == MatchPat::Wildcard {
                            if idx == 0 {
                                out.push_str(&format!("{}if (true) {{\n", pad));
                            } else {
                                out.push_str(" else {\n");
                            }
                        } else {
                            let cond_str = format!("{} == {}", scrut, self.fmt_pat(&arm.pat));
                            if idx == 0 {
                                out.push_str(&format!("{}if ({}) {{\n", pad, cond_str));
                            } else {
                                out.push_str(&format!(" else if ({}) {{\n", cond_str));
                            }
                        }
                        let saved = self.local_env.clone();
                        for s in &arm.body {
                            self.fmt_stmt(s, indent + 1, out);
                        }
                        self.local_env = saved;
                        out.push_str(&format!("{}}}", pad));
                    }
                    out.push('\n');
                } else {
                    out.push_str(&format!("{}switch ({}) {{\n", pad, self.fmt_expr(expr)));
                    let arm_pad = "    ".repeat(indent + 1);
                    let body_pad = "    ".repeat(indent + 2);
                    for arm in arms {
                        if arm.pat == MatchPat::Wildcard {
                            out.push_str(&format!("{}default: {{\n", arm_pad));
                        } else {
                            out.push_str(&format!(
                                "{}case {}: {{\n",
                                arm_pad,
                                self.fmt_pat(&arm.pat)
                            ));
                        }
                        let saved = self.local_env.clone();
                        for s in &arm.body {
                            self.fmt_stmt(s, indent + 2, out);
                        }
                        self.local_env = saved;
                        let ends_jump = matches!(
                            arm.body.last(),
                            Some(Stmt::Return { .. } | Stmt::Break { .. } | Stmt::Continue { .. })
                        );
                        if !ends_jump {
                            out.push_str(&format!("{}break;\n", body_pad));
                        }
                        out.push_str(&format!("{}}}\n", arm_pad));
                    }
                    out.push_str(&format!("{}}}\n", pad));
                }
            }
            Stmt::While { cond, body, .. } => {
                out.push_str(&format!("{}while ({}) {{\n", pad, self.fmt_expr(cond)));
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
                    "{}for (const auto& {} : {}) {{\n",
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
                    "{}for (int64_t {} = {}; {} < {}; {}++) {{\n",
                    pad,
                    var,
                    self.fmt_clean_int(start),
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
            Stmt::Break { .. } => out.push_str(&format!("{}break;\n", pad)),
            Stmt::Continue { .. } => out.push_str(&format!("{}continue;\n", pad)),
            Stmt::Return { value, .. } => match value {
                Some(v) => out.push_str(&format!("{}return {};\n", pad, self.fmt_expr(v))),
                None => out.push_str(&format!("{}return;\n", pad)),
            },
            Stmt::Assert { cond, .. } => {
                let s = self.fmt_expr(cond);
                if s.contains('{') {
                    out.push_str(&format!("{}assert(({}));\n", pad, s));
                } else {
                    out.push_str(&format!("{}assert({});\n", pad, s));
                }
            }
            Stmt::AssertEq { left, right, .. } => {
                let eq_expr = Expr::Binary {
                    op: BinOp::Eq,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                let s = self.fmt_expr(&eq_expr);
                if s.contains('{') {
                    out.push_str(&format!("{}assert(({}));\n", pad, s));
                } else {
                    out.push_str(&format!("{}assert({});\n", pad, s));
                }
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
            out.push_str(&format!("{}if ({}) {{\n", pad, self.fmt_expr(cond)));
        } else {
            out.push_str(&format!(" else if ({}) {{\n", self.fmt_expr(cond)));
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
            Expr::Intrinsic(intr) if matches!(intr.as_ref(), Intrinsic::Contains { .. }) => {
                format!("({})", s)
            }
            _ => s,
        }
    }

    fn fmt_print_arg(&self, expr: &Expr) -> String {
        match expr {
            Expr::Str(s) => format!("\"{}\"", escape_str(s)),
            Expr::Binary { op, .. } if binop_prec(*op) <= 3 => format!("({})", self.fmt_expr(expr)),
            Expr::Intrinsic(intr) if matches!(intr.as_ref(), Intrinsic::Contains { .. }) => {
                format!("({})", self.fmt_expr(expr))
            }
            _ => self.fmt_clean_int(expr),
        }
    }

    fn fmt_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => format!("int64_t({})", v),
            Expr::Float(v) => format_float(*v),
            Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Expr::Str(s) => format!("std::string(\"{}\")", escape_str(s)),
            Expr::Var(v) => v.clone(),
            Expr::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
            Expr::List(items) => {
                let elem_ty = items
                    .first()
                    .and_then(|e| self.expr_ty(e))
                    .unwrap_or(Type::Int);
                let inner: Vec<String> = items.iter().map(|e| self.fmt_clean_int(e)).collect();
                format!("std::vector<{}>{{{}}}", Self::fmt_type(&elem_ty), inner.join(", "))
            }
            Expr::StructInit { name, fields } => {
                let inner: Vec<String> = fields.iter().map(|(_, fval)| self.fmt_expr(fval)).collect();
                format!("{}{{{}}}", name, inner.join(", "))
            }
            Expr::FieldAccess { base, field } => format!("{}.{}", self.fmt_postfix(base), field),
            Expr::Index { base, index } => {
                format!("{}[{}]", self.fmt_postfix(base), self.fmt_clean_int(index))
            }
            Expr::Unary { op, expr: inner } => {
                if *op == UnaryOp::Neg {
                    if let Expr::Int(v) = inner.as_ref() {
                        return format!("int64_t(-{})", v);
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
                    Expr::Intrinsic(intr)
                        if matches!(intr.as_ref(), Intrinsic::Contains { .. }) =>
                    {
                        format!("{}({})", sym, self.fmt_expr(inner))
                    }
                    _ => format!("{}{}", sym, self.fmt_expr(inner)),
                }
            }
            Expr::Binary { op, left, right } => {
                let fmt_cmp_empty_list = |side: &Expr, peer: &Expr| -> Option<String> {
                    if matches!(op, BinOp::Eq | BinOp::Ne) {
                        if let Expr::List(items) = side {
                            if items.is_empty() {
                                if let Some(Type::List(elem)) = self.expr_ty(peer) {
                                    return Some(format!("std::vector<{}>{{}}", Self::fmt_type(&elem)));
                                }
                            }
                        }
                    }
                    None
                };
                let is_cpp_contains = |e: &Expr| {
                    matches!(
                        e,
                        Expr::Intrinsic(intr) if matches!(intr.as_ref(), Intrinsic::Contains { .. })
                    )
                };
                let l_raw = fmt_cmp_empty_list(left, right).unwrap_or_else(|| self.fmt_clean_int(left));
                let r_raw = fmt_cmp_empty_list(right, left).unwrap_or_else(|| self.fmt_clean_int(right));
                let l_str = if needs_parens(left, *op, false)
                    || (is_cpp_contains(left) && binop_prec(*op) >= 3)
                {
                    format!("({})", l_raw)
                } else {
                    l_raw
                };
                let r_str = if needs_parens(right, *op, true)
                    || (is_cpp_contains(right) && binop_prec(*op) >= 3)
                {
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
                    format!("int64_t({} {} {})", l_str, op_str, r_str)
                } else {
                    format!("{} {} {}", l_str, op_str, r_str)
                }
            }
            Expr::Call { func, args } => {
                let inner: Vec<String> = args.iter().map(|a| self.fmt_expr(a)).collect();
                format!("{}({})", func, inner.join(", "))
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e) => {
                    format!("static_cast<int64_t>({}.size())", self.fmt_postfix(e))
                }
                Intrinsic::Min(a, b) => {
                    format!("std::min({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Max(a, b) => {
                    format!("std::max({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Abs(a) => format!("std::abs({})", self.fmt_expr(a)),
                Intrinsic::Push { list, value } => {
                    format!("{}.push_back({})", self.fmt_postfix(list), self.fmt_expr(value))
                }
                Intrinsic::Print(args) => {
                    if args.is_empty() {
                        "std::cout << \"\\n\"".to_string()
                    } else {
                        let mut parts = Vec::with_capacity(args.len() * 2 + 1);
                        for (idx, a) in args.iter().enumerate() {
                            if idx > 0 {
                                parts.push("\" \"".to_string());
                            }
                            parts.push(self.fmt_print_arg(a));
                        }
                        parts.push("\"\\n\"".to_string());
                        format!("std::cout << {}", parts.join(" << "))
                    }
                }
                Intrinsic::Contains { haystack, needle } => {
                    if matches!(self.expr_ty(haystack), Some(Type::List(_))) {
                        let h = self.fmt_postfix(haystack);
                        format!(
                            "std::find({}.begin(), {}.end(), {}) != {}.end()",
                            h,
                            h,
                            self.fmt_expr(needle),
                            h
                        )
                    } else {
                        format!(
                            "{}.find({}) != std::string::npos",
                            self.fmt_postfix(haystack),
                            self.fmt_expr(needle)
                        )
                    }
                }
                Intrinsic::Upper(e) => format!("star_to_upper({})", self.fmt_expr(e)),
                Intrinsic::Lower(e) => format!("star_to_lower({})", self.fmt_expr(e)),
                Intrinsic::ToStr(e) => {
                    if self.expr_ty(e) == Some(Type::Str) {
                        format!("std::string({})", self.fmt_expr(e))
                    } else {
                        format!("std::to_string({})", self.fmt_clean_int(e))
                    }
                }
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
}

// ============================================================================
// C++ Lexer & Recursive-Descent Parser (`put`)
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
enum CTokKind {
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
    Amp,
    AmpAmp,
    PipePipe,
    Bang,
    Plus,
    PlusPlus,
    Minus,
    Star,
    Slash,
    Percent,
    Eq,
    EqEq,
    BangEq,
    Lt,
    Shl,
    Le,
    Gt,
    Ge,
    PlusEq,
    MinusEq,
}

#[derive(Debug, Clone)]
struct CTok {
    kind: CTokKind,
    line: usize,
    col: usize,
}

fn lex_cpp(src: &str) -> Result<Vec<CTok>, Diagnostic> {
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
        // Skip `#include ...` preprocessor directives
        if ch == '#' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
                col += 1;
            }
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
            tokens.push(CTok {
                kind: CTokKind::Comment(text),
                line,
                col: s_col,
            });
            continue;
        }
        if ch == '/' && i + 1 < chars.len() && chars[i + 1] == '*' {
            i += 2;
            col += 2;
            while i + 1 < chars.len() && !(chars[i] == '*' && chars[i + 1] == '/') {
                if chars[i] == '\n' {
                    line += 1;
                    col = 1;
                } else {
                    col += 1;
                }
                i += 1;
            }
            if i + 1 < chars.len() {
                i += 2;
                col += 2;
            }
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
                    "cpp",
                    "unterminated string literal",
                    s_line,
                    s_col,
                ));
            }
            tokens.push(CTok {
                kind: CTokKind::Str(unescape_string(&raw)),
                line: s_line,
                col: s_col,
            });
            continue;
        }
        if ch.is_ascii_digit() {
            let s_col = col;
            let start = i;
            let mut is_float = false;
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '\'') {
                i += 1;
                col += 1;
            }
            if i + 1 < chars.len() && chars[i] == '.' && chars[i + 1].is_ascii_digit() {
                is_float = true;
                i += 1;
                col += 1;
                while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '\'') {
                    i += 1;
                    col += 1;
                }
            }
            // Optional integer suffixes like `LL` or `L`
            while !is_float && i < chars.len() && matches!(chars[i], 'l' | 'L' | 'u' | 'U') {
                i += 1;
                col += 1;
            }
            let num_str: String = chars[start..i]
                .iter()
                .filter(|c| **c != '\'' && !matches!(**c, 'l' | 'L' | 'u' | 'U'))
                .collect();
            if is_float {
                let v = num_str
                    .parse::<f64>()
                    .map_err(|_| Diagnostic::new("cpp", "invalid float literal", line, s_col))?;
                tokens.push(CTok {
                    kind: CTokKind::Float(v),
                    line,
                    col: s_col,
                });
            } else {
                let v = num_str
                    .parse::<i64>()
                    .map_err(|_| Diagnostic::new("cpp", "invalid integer literal", line, s_col))?;
                tokens.push(CTok {
                    kind: CTokKind::Int(v),
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
            tokens.push(CTok {
                kind: CTokKind::Ident(ident),
                line,
                col: s_col,
            });
            continue;
        }

        let s_col = col;
        if i + 1 < chars.len() {
            let two = match (chars[i], chars[i + 1]) {
                (':', ':') => Some(CTokKind::ColonColon),
                ('&', '&') => Some(CTokKind::AmpAmp),
                ('|', '|') => Some(CTokKind::PipePipe),
                ('+', '+') => Some(CTokKind::PlusPlus),
                ('=', '=') => Some(CTokKind::EqEq),
                ('!', '=') => Some(CTokKind::BangEq),
                ('<', '<') => Some(CTokKind::Shl),
                ('<', '=') => Some(CTokKind::Le),
                ('>', '=') => Some(CTokKind::Ge),
                ('+', '=') => Some(CTokKind::PlusEq),
                ('-', '=') => Some(CTokKind::MinusEq),
                _ => None,
            };
            if let Some(kind) = two {
                tokens.push(CTok {
                    kind,
                    line,
                    col: s_col,
                });
                i += 2;
                col += 2;
                continue;
            }
        }

        let single = match ch {
            '(' => Some(CTokKind::LParen),
            ')' => Some(CTokKind::RParen),
            '{' => Some(CTokKind::LBrace),
            '}' => Some(CTokKind::RBrace),
            '[' => Some(CTokKind::LBracket),
            ']' => Some(CTokKind::RBracket),
            ',' => Some(CTokKind::Comma),
            ';' => Some(CTokKind::Semi),
            ':' => Some(CTokKind::Colon),
            '.' => Some(CTokKind::Dot),
            '&' => Some(CTokKind::Amp),
            '!' => Some(CTokKind::Bang),
            '+' => Some(CTokKind::Plus),
            '-' => Some(CTokKind::Minus),
            '*' => Some(CTokKind::Star),
            '/' => Some(CTokKind::Slash),
            '%' => Some(CTokKind::Percent),
            '=' => Some(CTokKind::Eq),
            '<' => Some(CTokKind::Lt),
            '>' => Some(CTokKind::Gt),
            _ => None,
        };
        if let Some(kind) = single {
            tokens.push(CTok {
                kind,
                line,
                col: s_col,
            });
            i += 1;
            col += 1;
        } else {
            return Err(Diagnostic::new(
                "cpp",
                format!("unexpected character '{}'", ch),
                line,
                s_col,
            ));
        }
    }

    Ok(tokens)
}

struct CppParser {
    tokens: Vec<CTok>,
    pos: usize,
    known_enums: HashSet<String>,
    struct_field_order: HashMap<String, Vec<String>>,
}

impl CppParser {
    fn peek(&self) -> Option<&CTok> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&CTokKind> {
        self.peek().map(|t| &t.kind)
    }

    fn cur_loc(&self) -> (usize, usize) {
        self.peek()
            .or_else(|| self.tokens.last())
            .map(|t| (t.line, t.col))
            .unwrap_or((1, 1))
    }

    fn err<T>(&self, msg: impl Into<String>) -> Result<T, Diagnostic> {
        let (l, c) = self.cur_loc();
        Err(Diagnostic::new("cpp", msg, l, c))
    }

    fn next(&mut self) -> Option<CTok> {
        let tok = self.tokens.get(self.pos).cloned();
        if tok.is_some() {
            self.pos += 1;
        }
        tok
    }

    fn eat(&mut self, kind: &CTokKind) -> bool {
        if self.peek_kind() == Some(kind) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: &CTokKind, expected: &str) -> Result<(), Diagnostic> {
        if self.eat(kind) {
            Ok(())
        } else {
            self.err(format!("expected {}", expected))
        }
    }

    fn expect_ident(&mut self) -> Result<String, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(CTokKind::Ident(s)) => {
                self.pos += 1;
                Ok(s)
            }
            _ => self.err("expected identifier"),
        }
    }

    fn skip_balanced_braces(&mut self) -> Result<(), Diagnostic> {
        self.expect(&CTokKind::LBrace, "'{'")?;
        let mut depth = 1usize;
        while depth > 0 {
            match self.next().map(|t| t.kind) {
                Some(CTokKind::LBrace) => depth += 1,
                Some(CTokKind::RBrace) => depth -= 1,
                Some(_) => {}
                None => return self.err("unclosed '{' in inline helper"),
            }
        }
        Ok(())
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut module = HubModule::new();
        let mut comments = Vec::new();

        while self.peek().is_some() {
            if let Some(CTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.next();
                comments.push(c);
                continue;
            }
            if self.eat(&CTokKind::Semi) {
                continue;
            }
            // Skip generated `inline std::string star_to_lower/upper(...) { ... }` prelude helpers
            if self.eat_kw("inline") {
                comments.clear();
                while self.peek().is_some() && !matches!(self.peek_kind(), Some(CTokKind::LBrace)) {
                    self.next();
                }
                self.skip_balanced_braces()?;
                continue;
            }

            let item_comments = std::mem::take(&mut comments);
            if self.eat_kw("struct") {
                let s = self.parse_struct(item_comments)?;
                self.struct_field_order
                    .insert(s.name.clone(), s.fields.iter().map(|f| f.name.clone()).collect());
                module.items.push(Item::Struct(s));
            } else if self.eat_kw("enum") {
                let e = self.parse_enum(item_comments)?;
                self.known_enums.insert(e.name.clone());
                module.items.push(Item::Enum(e));
            } else {
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
            }
        }

        Ok(module)
    }

    fn parse_struct(&mut self, comments: Vec<String>) -> Result<StructDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&CTokKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
            if let Some(CTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "bool")
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(CTokKind::Ident(op)) if op == "operator"
                )
            {
                while self.peek().is_some() && !matches!(self.peek_kind(), Some(CTokKind::LBrace)) {
                    self.next();
                }
                self.skip_balanced_braces()?;
                continue;
            }
            let fty = self.parse_type()?;
            let fname = self.expect_ident()?;
            self.expect(&CTokKind::Semi, "';'")?;
            fields.push(Field {
                id: 0,
                name: fname,
                ty: fty,
                meta: Metadata::new(),
            });
        }
        self.expect(&CTokKind::RBrace, "'}'")?;
        let _ = self.eat(&CTokKind::Semi);
        Ok(StructDecl {
            id: 0,
            name,
            fields,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_enum(&mut self, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        let _ = self.eat_kw("class");
        let name = self.expect_ident()?;
        if self.eat(&CTokKind::Colon) {
            let _ = self.parse_type()?;
        }
        self.expect(&CTokKind::LBrace, "'{'")?;
        let mut variants = Vec::new();
        while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
            if let Some(CTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            let vname = self.expect_ident()?;
            if self.eat(&CTokKind::Eq) {
                let _ = self.parse_expr()?;
            }
            variants.push(vname);
            if !self.eat(&CTokKind::Comma) {
                break;
            }
        }
        self.expect(&CTokKind::RBrace, "'}'")?;
        let _ = self.eat(&CTokKind::Semi);
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta: Metadata::new(),
        })
    }

    fn is_ref_default_ty(&self, ty: &Type) -> bool {
        match ty {
            Type::List(_) | Type::Str => true,
            Type::Named(n) => !self.known_enums.contains(n),
            _ => false,
        }
    }

    fn parse_fn(&mut self, comments: Vec<String>) -> Result<FnDecl, Diagnostic> {
        let raw_ret_ty = self.parse_type()?;
        let name = self.expect_ident()?;
        self.expect(&CTokKind::LParen, "'('")?;
        let mut params = Vec::new();
        while !matches!(self.peek_kind(), Some(CTokKind::RParen) | None) {
            let _ = self.eat_kw("const");
            let pty = self.parse_type()?;
            let by_ref = self.eat(&CTokKind::Amp);
            let pname = self.expect_ident()?;
            let mut meta = Metadata::new();
            if self.is_ref_default_ty(&pty) && !by_ref {
                meta.insert("cpp.pass".to_string(), "value".to_string());
            }
            params.push(Param {
                id: 0,
                name: pname,
                ty: pty,
                meta,
            });
            if !self.eat(&CTokKind::Comma) {
                break;
            }
        }
        self.expect(&CTokKind::RParen, "')'")?;

        let ret_ty = if name == "main" {
            Type::Void
        } else {
            raw_ret_ty
        };

        let mut body = self.parse_block()?;
        if name == "main" {
            if matches!(
                body.last(),
                Some(Stmt::Return {
                    value: Some(Expr::Int(0)),
                    ..
                })
            ) {
                body.pop();
            }
        } else if ret_ty != Type::Void
            && matches!(
                body.last(),
                Some(Stmt::Expr {
                    expr: Expr::Call { func, args },
                    ..
                }) if func == "__builtin_unreachable" && args.is_empty()
            ) {
                body.pop();
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
        let first = self.expect_ident()?;
        if first == "std" && self.eat(&CTokKind::ColonColon) {
            let member = self.expect_ident()?;
            return match member.as_str() {
                "string" => Ok(Type::Str),
                "vector" => {
                    self.expect(&CTokKind::Lt, "'<' after std::vector")?;
                    let inner = self.parse_type()?;
                    self.expect(&CTokKind::Gt, "'>' closing std::vector")?;
                    Ok(Type::list(inner))
                }
                other => self.err(format!("unsupported C++ type 'std::{}'", other)),
            };
        }

        Ok(match first.as_str() {
            "int" | "int64_t" | "int32_t" | "long" => Type::Int,
            "double" | "float" => Type::Float,
            "bool" => Type::Bool,
            "string" => Type::Str,
            "void" => Type::Void,
            other => Type::Named(other.to_string()),
        })
    }

    fn can_start_var_decl(&self) -> bool {
        let mut p = self.pos;
        if matches!(self.tokens.get(p).map(|t| &t.kind), Some(CTokKind::Ident(s)) if s == "const") {
            return true;
        }
        if matches!(self.tokens.get(p).map(|t| &t.kind), Some(CTokKind::Ident(s)) if s == "auto") {
            return true;
        }
        // Check `<type> <ident> =`
        match self.tokens.get(p).map(|t| &t.kind) {
            Some(CTokKind::Ident(s)) if s == "std" => {
                if self.tokens.get(p + 1).map(|t| &t.kind) != Some(&CTokKind::ColonColon) {
                    return false;
                }
                match self.tokens.get(p + 2).map(|t| &t.kind) {
                    Some(CTokKind::Ident(m)) if m == "string" => {
                        matches!(
                            self.tokens.get(p + 3).map(|t| &t.kind),
                            Some(CTokKind::Ident(_))
                        )
                    }
                    Some(CTokKind::Ident(m)) if m == "vector" => {
                        p += 3;
                        if self.tokens.get(p).map(|t| &t.kind) != Some(&CTokKind::Lt) {
                            return false;
                        }
                        let mut depth = 0i32;
                        while let Some(tok) = self.tokens.get(p) {
                            if tok.kind == CTokKind::Lt {
                                depth += 1;
                            } else if tok.kind == CTokKind::Gt {
                                depth -= 1;
                                if depth == 0 {
                                    p += 1;
                                    break;
                                }
                            }
                            p += 1;
                        }
                        matches!(self.tokens.get(p).map(|t| &t.kind), Some(CTokKind::Ident(_)))
                    }
                    _ => false,
                }
            }
            Some(CTokKind::Ident(s)) => {
                let is_known_ty = matches!(
                    s.as_str(),
                    "int" | "int64_t" | "int32_t" | "double" | "float" | "bool"
                ) || self.struct_field_order.contains_key(s)
                    || self.known_enums.contains(s);
                is_known_ty
                    && matches!(
                        self.tokens.get(p + 1).map(|t| &t.kind),
                        Some(CTokKind::Ident(_))
                    )
            }
            _ => false,
        }
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        self.expect(&CTokKind::LBrace, "'{'")?;
        let mut stmts = Vec::new();
        while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
            stmts.push(self.parse_stmt()?);
        }
        self.expect(&CTokKind::RBrace, "'}'")?;
        Ok(stmts)
    }

    fn parse_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        if let Some(CTokKind::Comment(c)) = self.peek_kind().cloned() {
            self.next();
            if c.trim() == "@star-match" && self.eat_kw("if") {
                return self.parse_star_string_match();
            }
            return Ok(Stmt::Comment { id: 0, text: c });
        }

        if self.eat_kw("if") {
            return self.parse_if();
        }
        if self.eat_kw("switch") {
            return self.parse_switch();
        }
        if self.eat_kw("while") {
            self.expect(&CTokKind::LParen, "'(' after while")?;
            let cond = self.parse_expr()?;
            self.expect(&CTokKind::RParen, "')'")?;
            let body = self.parse_block()?;
            return Ok(Stmt::While {
                id: 0,
                cond,
                body,
                meta: Metadata::new(),
            });
        }
        if self.eat_kw("for") {
            return self.parse_for();
        }
        if self.eat_kw("break") {
            self.expect(&CTokKind::Semi, "';'")?;
            return Ok(Stmt::Break { id: 0 });
        }
        if self.eat_kw("continue") {
            self.expect(&CTokKind::Semi, "';'")?;
            return Ok(Stmt::Continue { id: 0 });
        }
        if self.eat_kw("return") {
            if self.eat(&CTokKind::Semi) {
                return Ok(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                });
            }
            let val = self.parse_expr()?;
            self.expect(&CTokKind::Semi, "';'")?;
            return Ok(Stmt::Return {
                id: 0,
                value: Some(val),
                meta: Metadata::new(),
            });
        }

        if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "assert")
            && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&CTokKind::LParen)
        {
            self.pos += 2;
            let cond = self.parse_expr()?;
            self.expect(&CTokKind::RParen, "')' after assert")?;
            self.expect(&CTokKind::Semi, "';' after assert")?;
            return Ok(Stmt::Assert {
                id: 0,
                cond,
                meta: Metadata::new(),
            });
        }

        // `std::cout << a << " " << b << "\n";` -> `Intrinsic::Print`
        if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "std")
            && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&CTokKind::ColonColon)
            && matches!(
                self.tokens.get(self.pos + 2).map(|t| &t.kind),
                Some(CTokKind::Ident(m)) if m == "cout"
            )
        {
            self.pos += 3;
            let mut operands = Vec::new();
            while self.eat(&CTokKind::Shl) {
                if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "std")
                    && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&CTokKind::ColonColon)
                    && matches!(
                        self.tokens.get(self.pos + 2).map(|t| &t.kind),
                        Some(CTokKind::Ident(m)) if m == "endl"
                    )
                {
                    self.pos += 3;
                    operands.push(Expr::Str("\n".to_string()));
                } else {
                    operands.push(self.parse_add()?);
                }
            }
            self.expect(&CTokKind::Semi, "';' after std::cout")?;
            if matches!(operands.last(), Some(Expr::Str(s)) if s == "\n") {
                operands.pop();
            }
            let args = if operands.len() >= 3
                && operands.len() % 2 == 1
                && operands
                    .iter()
                    .skip(1)
                    .step_by(2)
                    .all(|e| matches!(e, Expr::Str(s) if s == " "))
            {
                operands.into_iter().step_by(2).collect()
            } else {
                operands
            };
            return Ok(Stmt::Expr {
                id: 0,
                expr: Expr::intrinsic(Intrinsic::Print(args)),
                meta: Metadata::new(),
            });
        }

        // Local declaration `[const] (auto | <Type>) name = expr;`
        if self.can_start_var_decl() {
            let is_const = self.eat_kw("const");
            let ty = if self.eat_kw("auto") {
                None
            } else {
                Some(self.parse_type()?)
            };
            let name = self.expect_ident()?;
            self.expect(&CTokKind::Eq, "'=' in variable declaration")?;
            let value = if self.eat(&CTokKind::LBrace) {
                self.expect(&CTokKind::RBrace, "'}'")?;
                Expr::List(Vec::new())
            } else {
                self.parse_expr()?
            };
            self.expect(&CTokKind::Semi, "';'")?;
            let mut meta = Metadata::new();
            if !is_const {
                meta.insert("explicit_mut".to_string(), "true".to_string());
            }
            return Ok(Stmt::Let {
                id: 0,
                name,
                mutable: !is_const,
                ty,
                value,
                meta,
            });
        }

        let expr = self.parse_expr()?;
        if let Some(op) = match self.peek_kind() {
            Some(CTokKind::Eq) => Some(AssignOp::Set),
            Some(CTokKind::PlusEq) => Some(AssignOp::AddAssign),
            Some(CTokKind::MinusEq) => Some(AssignOp::SubAssign),
            _ => None,
        } {
            self.next();
            let value = self.parse_expr()?;
            self.expect(&CTokKind::Semi, "';'")?;
            let target = cpp_expr_to_target(expr)?;
            return Ok(Stmt::Assign {
                id: 0,
                target,
                op,
                value,
                meta: Metadata::new(),
            });
        }

        self.expect(&CTokKind::Semi, "';'")?;
        Ok(Stmt::Expr {
            id: 0,
            expr,
            meta: Metadata::new(),
        })
    }

    fn parse_if(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&CTokKind::LParen, "'(' after if")?;
        let cond = self.parse_expr()?;
        self.expect(&CTokKind::RParen, "')'")?;
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
        Ok(Stmt::If {
            id: 0,
            cond,
            then_body,
            else_body,
            meta: Metadata::new(),
        })
    }

    fn parse_star_string_match(&mut self) -> Result<Stmt, Diagnostic> {
        let mut arms = Vec::new();
        let mut scrutinee: Option<Expr> = None;

        loop {
            self.expect(&CTokKind::LParen, "'('")?;
            let cond = self.parse_expr()?;
            self.expect(&CTokKind::RParen, "')'")?;
            let body = self.parse_block()?;

            if cond == Expr::Bool(true) {
                arms.push(MatchArm {
                    pat: MatchPat::Wildcard,
                    body,
                });
            } else if let Expr::Binary {
                op: BinOp::Eq,
                left,
                right,
            } = cond
            {
                if scrutinee.is_none() {
                    scrutinee = Some(*left);
                }
                let pat = match *right {
                    Expr::Str(s) => MatchPat::Str(s),
                    Expr::Int(v) => MatchPat::Int(v),
                    _ => return self.err("expected string literal in @star-match"),
                };
                arms.push(MatchArm { pat, body });
            } else {
                return self.err("invalid condition in @star-match");
            }

            if self.eat_kw("else") {
                if self.eat_kw("if") {
                    continue;
                } else {
                    let wild_body = self.parse_block()?;
                    arms.push(MatchArm {
                        pat: MatchPat::Wildcard,
                        body: wild_body,
                    });
                    break;
                }
            } else {
                break;
            }
        }

        Ok(Stmt::Match {
            id: 0,
            expr: scrutinee.unwrap_or(Expr::Str(String::new())),
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_switch(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&CTokKind::LParen, "'(' after switch")?;
        let expr = self.parse_expr()?;
        self.expect(&CTokKind::RParen, "')'")?;
        self.expect(&CTokKind::LBrace, "'{' after switch")?;

        let mut arms = Vec::new();
        while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
            let pat = if self.eat_kw("default") {
                self.expect(&CTokKind::Colon, "':' after default")?;
                MatchPat::Wildcard
            } else if self.eat_kw("case") {
                let pexpr = self.parse_expr()?;
                self.expect(&CTokKind::Colon, "':' after case")?;
                match pexpr {
                    Expr::EnumVariant { enum_name, variant } => {
                        MatchPat::EnumVariant { enum_name, variant }
                    }
                    Expr::Int(v) => MatchPat::Int(v),
                    Expr::Unary {
                        op: UnaryOp::Neg,
                        expr: inner,
                    } if matches!(inner.as_ref(), Expr::Int(_)) => {
                        if let Expr::Int(v) = *inner {
                            MatchPat::Int(-v)
                        } else {
                            unreachable!()
                        }
                    }
                    _ => return self.err("unsupported C++ switch case pattern"),
                }
            } else {
                return self.err("expected 'case' or 'default' in switch");
            };

            let mut body = if matches!(self.peek_kind(), Some(CTokKind::LBrace)) {
                self.parse_block()?
            } else {
                let mut stmts = Vec::new();
                while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None)
                    && !matches!(
                        self.peek_kind(),
                        Some(CTokKind::Ident(s)) if s == "case" || s == "default"
                    )
                {
                    stmts.push(self.parse_stmt()?);
                }
                stmts
            };

            // Strip C++ switch fallthrough guard `break;`
            if matches!(body.last(), Some(Stmt::Break { .. })) {
                body.pop();
            }
            arms.push(MatchArm { pat, body });
        }

        self.expect(&CTokKind::RBrace, "'}'")?;
        Ok(Stmt::Match {
            id: 0,
            expr,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_for(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&CTokKind::LParen, "'(' after for")?;
        let saved = self.pos;

        // Try range-based for: `for ([const] (auto|<Type>) [&] var : iter)`
        let _ = self.eat_kw("const");
        let parsed_head = if self.eat_kw("auto") {
            let _ = self.eat(&CTokKind::Amp);
            self.expect_ident().ok()
        } else if let Ok(_ty) = self.parse_type() {
            let _ = self.eat(&CTokKind::Amp);
            self.expect_ident().ok()
        } else {
            None
        };

        if let Some(var) = parsed_head {
            if self.eat(&CTokKind::Colon) {
                let iter = self.parse_expr()?;
                self.expect(&CTokKind::RParen, "')'")?;
                let body = self.parse_block()?;
                return Ok(Stmt::ForEach {
                    id: 0,
                    var,
                    iter,
                    body,
                    meta: Metadata::new(),
                });
            }
        }

        // Otherwise C-style range loop: `for (int64_t i = start; i < end; i++)`
        self.pos = saved;
        let _ = self.parse_type()?;
        let var = self.expect_ident()?;
        self.expect(&CTokKind::Eq, "'=' in C++ for loop")?;
        let start = self.parse_expr()?;
        self.expect(&CTokKind::Semi, "';' in C++ for loop")?;
        let cvar = self.expect_ident()?;
        if cvar != var {
            return self.err("for-loop condition variable must match loop variable");
        }
        self.expect(&CTokKind::Lt, "'<' in C++ for loop")?;
        let end = self.parse_expr()?;
        self.expect(&CTokKind::Semi, "';' in C++ for loop")?;
        let _ = self.expect_ident()?;
        if !self.eat(&CTokKind::PlusPlus) && self.eat(&CTokKind::PlusEq) {
            let _ = self.parse_expr()?;
        }
        self.expect(&CTokKind::RParen, "')'")?;
        let body = self.parse_block()?;
        Ok(Stmt::ForRange {
            id: 0,
            var,
            start,
            end,
            body,
            meta: Metadata::new(),
        })
    }

    fn parse_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_and()?;
        while self.eat(&CTokKind::PipePipe) {
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
        while self.eat(&CTokKind::AmpAmp) {
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
                Some(CTokKind::EqEq) => Some(BinOp::Eq),
                Some(CTokKind::BangEq) => Some(BinOp::Ne),
                Some(CTokKind::Lt) => Some(BinOp::Lt),
                Some(CTokKind::Le) => Some(BinOp::Le),
                Some(CTokKind::Gt) => Some(BinOp::Gt),
                Some(CTokKind::Ge) => Some(BinOp::Ge),
                _ => None,
            };
            if let Some(op) = op {
                self.next();
                let right = self.parse_add()?;

                // Recognize `s.find(needle) != std::string::npos` and `std::find(v.begin(), v.end(), needle) != v.end()`
                if op == BinOp::Ne {
                    if let (
                        Expr::Call {
                            func: lfunc,
                            args: largs,
                        },
                        Expr::Var(rvar),
                    ) = (&left, &right)
                    {
                        if lfunc == "__cpp_str_find" && largs.len() == 2 && rvar == "__cpp_npos" {
                            left = Expr::intrinsic(Intrinsic::Contains {
                                haystack: largs[0].clone(),
                                needle: largs[1].clone(),
                            });
                            continue;
                        }
                    }
                    if let (
                        Expr::Call {
                            func: lfunc,
                            args: largs,
                        },
                        Expr::Call {
                            func: rfunc,
                            args: rargs,
                        },
                    ) = (&left, &right)
                    {
                        if lfunc == "__cpp_std_find"
                            && largs.len() == 2
                            && rfunc == "__cpp_vec_end"
                            && rargs.len() == 1
                        {
                            left = Expr::intrinsic(Intrinsic::Contains {
                                haystack: largs[0].clone(),
                                needle: largs[1].clone(),
                            });
                            continue;
                        }
                    }
                }

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
                Some(CTokKind::Plus) => Some(BinOp::Add),
                Some(CTokKind::Minus) => Some(BinOp::Sub),
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
                Some(CTokKind::Star) => Some(BinOp::Mul),
                Some(CTokKind::Slash) => Some(BinOp::Div),
                Some(CTokKind::Percent) => Some(BinOp::Mod),
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
        if self.eat(&CTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        if self.eat(&CTokKind::Bang) {
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
            if self.eat(&CTokKind::Dot) {
                let member = self.expect_ident()?;
                if self.eat(&CTokKind::LParen) {
                    let mut args = self.parse_expr_list(&CTokKind::RParen)?;
                    base = match (member.as_str(), args.len()) {
                        ("size" | "length", 0) => Expr::intrinsic(Intrinsic::Len(base)),
                        ("push_back", 1) => Expr::intrinsic(Intrinsic::Push {
                            list: base,
                            value: args.pop().unwrap(),
                        }),
                        ("find", 1) => Expr::Call {
                            func: "__cpp_str_find".to_string(),
                            args: vec![base, args.pop().unwrap()],
                        },
                        ("begin", 0) => Expr::Call {
                            func: "__cpp_vec_begin".to_string(),
                            args: vec![base],
                        },
                        ("end", 0) => Expr::Call {
                            func: "__cpp_vec_end".to_string(),
                            args: vec![base],
                        },
                        _ => {
                            return self.err(format!(
                                "unsupported C++ method '.{}(...)'",
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
            } else if self.eat(&CTokKind::LBracket) {
                let idx = self.parse_expr()?;
                self.expect(&CTokKind::RBracket, "']'")?;
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
            Some(CTokKind::Int(v)) => {
                self.next();
                Ok(Expr::Int(v))
            }
            Some(CTokKind::Float(v)) => {
                self.next();
                Ok(Expr::Float(v))
            }
            Some(CTokKind::Str(s)) => {
                self.next();
                Ok(Expr::Str(s))
            }
            Some(CTokKind::LParen) => {
                self.next();
                let e = self.parse_expr()?;
                self.expect(&CTokKind::RParen, "')'")?;
                Ok(e)
            }
            Some(CTokKind::Ident(ident)) => {
                self.next();
                if ident == "true" {
                    return Ok(Expr::Bool(true));
                }
                if ident == "false" {
                    return Ok(Expr::Bool(false));
                }
                if ident == "static_cast" {
                    self.expect(&CTokKind::Lt, "'<' after static_cast")?;
                    let _ = self.parse_type()?;
                    self.expect(&CTokKind::Gt, "'>' after static_cast type")?;
                    self.expect(&CTokKind::LParen, "'('")?;
                    let inner = self.parse_expr()?;
                    self.expect(&CTokKind::RParen, "')'")?;
                    return Ok(inner);
                }
                if ident == "std" && self.eat(&CTokKind::ColonColon) {
                    let member = self.expect_ident()?;
                    match member.as_str() {
                        "vector" => {
                            self.expect(&CTokKind::Lt, "'<'")?;
                            let _ = self.parse_type()?;
                            self.expect(&CTokKind::Gt, "'>'")?;
                            self.expect(&CTokKind::LBrace, "'{'")?;
                            let items = self.parse_expr_list(&CTokKind::RBrace)?;
                            return Ok(Expr::List(items));
                        }
                        "string" => {
                            if self.eat(&CTokKind::ColonColon) {
                                let sub = self.expect_ident()?;
                                if sub == "npos" {
                                    return Ok(Expr::Var("__cpp_npos".to_string()));
                                }
                                return self.err(format!("unsupported 'std::string::{}'", sub));
                            }
                            self.expect(&CTokKind::LParen, "'(' after std::string")?;
                            let mut args = self.parse_expr_list(&CTokKind::RParen)?;
                            if args.len() == 1 {
                                let inner = args.pop().unwrap();
                                return match inner {
                                    Expr::Str(_) => Ok(inner),
                                    other => Ok(Expr::intrinsic(Intrinsic::ToStr(other))),
                                };
                            }
                            return Ok(Expr::Str(String::new()));
                        }
                        "min" | "max" | "abs" | "to_string" | "find" => {
                            // Optional explicit template arg `std::min<int64_t>(...)`
                            if self.eat(&CTokKind::Lt) {
                                let _ = self.parse_type()?;
                                self.expect(&CTokKind::Gt, "'>'")?;
                            }
                            self.expect(&CTokKind::LParen, "'('")?;
                            let mut args = self.parse_expr_list(&CTokKind::RParen)?;
                            return match (member.as_str(), args.len()) {
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
                                ("abs", 1) => Ok(Expr::intrinsic(Intrinsic::Abs(args.pop().unwrap()))),
                                ("to_string", 1) => {
                                    Ok(Expr::intrinsic(Intrinsic::ToStr(args.pop().unwrap())))
                                }
                                ("find", 3) => {
                                    let needle = args.pop().unwrap();
                                    let _end = args.pop().unwrap();
                                    let begin = args.pop().unwrap();
                                    let haystack = match begin {
                                        Expr::Call { mut args, .. } if !args.is_empty() => {
                                            args.pop().unwrap()
                                        }
                                        other => other,
                                    };
                                    Ok(Expr::Call {
                                        func: "__cpp_std_find".to_string(),
                                        args: vec![haystack, needle],
                                    })
                                }
                                _ => self.err(format!("invalid call to 'std::{}'", member)),
                            };
                        }
                        other => return self.err(format!("unsupported 'std::{}'", other)),
                    }
                }

                // `EnumName::Variant`
                if self.eat(&CTokKind::ColonColon) {
                    let variant = self.expect_ident()?;
                    return Ok(Expr::EnumVariant {
                        enum_name: ident,
                        variant,
                    });
                }

                // Function call or cast `int64_t(x)`, `star_to_lower(s)`, `foo(a, b)`
                if self.eat(&CTokKind::LParen) {
                    let mut args = self.parse_expr_list(&CTokKind::RParen)?;
                    return match (ident.as_str(), args.len()) {
                        ("int64_t" | "int" | "double", 1) => Ok(args.pop().unwrap()),
                        ("star_to_lower", 1) => {
                            Ok(Expr::intrinsic(Intrinsic::Lower(args.pop().unwrap())))
                        }
                        ("star_to_upper", 1) => {
                            Ok(Expr::intrinsic(Intrinsic::Upper(args.pop().unwrap())))
                        }
                        _ => Ok(Expr::Call { func: ident, args }),
                    };
                }

                // Struct aggregate or designated initializer `Summary{count, total, avg}` or `Summary{.count = count, ...}`
                if ident
                    .chars()
                    .next()
                    .map(|c| c.is_ascii_uppercase())
                    .unwrap_or(false)
                    && self.eat(&CTokKind::LBrace)
                {
                    let mut fields = Vec::new();
                    let known_order = self.struct_field_order.get(&ident).cloned();
                    let mut idx = 0usize;
                    while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
                        let (fname, fval) = if self.eat(&CTokKind::Dot) {
                            let n = self.expect_ident()?;
                            self.expect(&CTokKind::Eq, "'=' in designated initializer")?;
                            let v = self.parse_expr()?;
                            (n, v)
                        } else {
                            let v = self.parse_expr()?;
                            let n = known_order
                                .as_ref()
                                .and_then(|ord| ord.get(idx).cloned())
                                .unwrap_or_else(|| format!("field_{}", idx));
                            (n, v)
                        };
                        fields.push((fname, fval));
                        idx += 1;
                        if !self.eat(&CTokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&CTokKind::RBrace, "'}'")?;
                    return Ok(Expr::StructInit {
                        name: ident,
                        fields,
                    });
                }

                Ok(Expr::Var(ident))
            }
            _ => self.err("expected C++ expression"),
        }
    }

    fn parse_expr_list(&mut self, closing: &CTokKind) -> Result<Vec<Expr>, Diagnostic> {
        let mut items = Vec::new();
        while self.peek_kind() != Some(closing) && self.peek().is_some() {
            items.push(self.parse_expr()?);
            if !self.eat(&CTokKind::Comma) {
                break;
            }
        }
        self.expect(closing, "closing ')' or '}'")?;
        Ok(items)
    }
}

fn cpp_expr_to_target(expr: Expr) -> Result<AssignTarget, Diagnostic> {
    match expr {
        Expr::Var(v) => Ok(AssignTarget::Var(v)),
        Expr::FieldAccess { base, field } => {
            if let Expr::Var(b) = *base {
                Ok(AssignTarget::Field { base: b, field })
            } else {
                Err(Diagnostic::new(
                    "cpp",
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
                    "cpp",
                    "nested index assignment not supported",
                    1,
                    1,
                ))
            }
        }
        _ => Err(Diagnostic::new("cpp", "invalid assignment target", 1, 1)),
    }
}

fn cpp_block_terminates(stmts: &[Stmt]) -> bool {
    stmts
        .iter()
        .rev()
        .find(|s| !matches!(s, Stmt::Comment { .. }))
        .map(cpp_stmt_terminates)
        .unwrap_or(false)
}

fn cpp_stmt_terminates(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Return { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            !else_body.is_empty()
                && cpp_block_terminates(then_body)
                && cpp_block_terminates(else_body)
        }
        Stmt::Match { arms, .. } => {
            arms.iter().any(|a| a.pat == MatchPat::Wildcard)
                && arms
                    .iter()
                    .all(|a| cpp_block_terminates(&a.body) && !cpp_stmts_have_break(&a.body))
        }
        _ => false,
    }
}

fn cpp_stmts_have_break(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Break { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => cpp_stmts_have_break(then_body) || cpp_stmts_have_break(else_body),
        _ => false,
    })
}

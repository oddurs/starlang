use std::collections::{HashMap, HashSet};

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl,
    HubModule, Intrinsic, Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl,
    Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct TypeScriptLens;

impl LanguageLens for TypeScriptLens {
    fn id(&self) -> SpokeId {
        SpokeId::TypeScript
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut ctx = TsFmtCtx::from_hub(hub);
        let mut out = String::new();
        for (idx, item) in hub.items.iter().enumerate() {
            if idx > 0 {
                out.push('\n');
            }
            match item {
                Item::Struct(s) => fmt_struct(s, &mut out),
                Item::Enum(e) => fmt_enum(e, &mut out),
                Item::Function(f) => ctx.fmt_fn(f, &mut out),
                Item::Test(t) => ctx.fmt_test(t, &mut out),
            }
        }
        if hub.has_main() {
            out.push_str("\nmain();\n");
        }
        out
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_ts(source)?;
        let mut known_structs: HashMap<String, Vec<String>> = HashMap::new();
        for item in &prev_hub.items {
            if let Item::Struct(s) = item {
                known_structs.insert(
                    s.name.clone(),
                    s.fields.iter().map(|f| f.name.clone()).collect(),
                );
            }
        }
        let mut parser = TsParser {
            tokens,
            pos: 0,
            known_structs,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::TypeScript))
    }
}

fn fmt_type(ty: &Type) -> String {
    match ty {
        Type::Int | Type::Float => "number".to_string(),
        Type::Bool => "boolean".to_string(),
        Type::Str => "string".to_string(),
        Type::Void => "void".to_string(),
        Type::List(inner) => format!("{}[]", fmt_type(inner)),
        Type::Named(name) => name.clone(),
    }
}

fn fmt_struct(s: &StructDecl, out: &mut String) {
    for c in &s.comments {
        out.push_str(&format!("// {}\n", c));
    }
    out.push_str(&format!("export interface {} {{\n", s.name));
    for f in &s.fields {
        out.push_str(&format!("  {}: {};\n", f.name, fmt_type(&f.ty)));
    }
    out.push_str("}\n");
}

fn fmt_enum(e: &EnumDecl, out: &mut String) {
    for c in &e.comments {
        out.push_str(&format!("// {}\n", c));
    }
    out.push_str(&format!("export const {} = {{\n", e.name));
    for (i, v) in e.variants.iter().enumerate() {
        out.push_str(&format!("  {}: {},\n", v, i));
    }
    out.push_str("} as const;\n");
    out.push_str(&format!(
        "export type {} = (typeof {})[keyof typeof {}];\n",
        e.name, e.name, e.name
    ));
}

fn fmt_pat(pat: &MatchPat) -> String {
    match pat {
        MatchPat::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
        MatchPat::Int(v) => v.to_string(),
        MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
        MatchPat::Wildcard => "default".to_string(),
    }
}

struct TsFmtCtx {
    fn_ret_types: HashMap<String, Type>,
    struct_fields: HashMap<String, HashMap<String, Type>>,
    enum_names: HashSet<String>,
    local_env: HashMap<String, Type>,
}

impl TsFmtCtx {
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

    fn expr_needs_deep_eq(&self, expr: &Expr) -> bool {
        if matches!(expr, Expr::List(_) | Expr::StructInit { .. }) {
            return true;
        }
        match self.expr_ty(expr) {
            Some(Type::List(_)) => true,
            Some(Type::Named(name)) => !self.enum_names.contains(&name),
            _ => false,
        }
    }

    fn fmt_fn(&mut self, f: &FnDecl, out: &mut String) {
        for c in &f.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        for p in &f.params {
            self.local_env.insert(p.name.clone(), p.ty.clone());
        }
        let export_kw = if f.name == "main" { "" } else { "export " };
        let params_str: Vec<String> = f
            .params
            .iter()
            .map(|p| format!("{}: {}", p.name, fmt_type(&p.ty)))
            .collect();
        out.push_str(&format!(
            "{}function {}({}): {} {{\n",
            export_kw,
            f.name,
            params_str.join(", "),
            fmt_type(&f.ret_ty)
        ));
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
        out.push_str(&format!("export function test_{}(): void {{\n", t.name));
        for stmt in &t.body {
            self.fmt_stmt(stmt, 1, out);
        }
        out.push_str("}\n");
    }

    fn fmt_stmt(&mut self, stmt: &Stmt, indent: usize, out: &mut String) {
        let pad = "  ".repeat(indent);
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
                let kw = if *mutable { "let" } else { "const" };
                let val_str = self.fmt_expr(value);
                if let Some(t) = ty {
                    self.local_env.insert(name.clone(), t.clone());
                    out.push_str(&format!(
                        "{}{} {}: {} = {};\n",
                        pad,
                        kw,
                        name,
                        fmt_type(t),
                        val_str
                    ));
                } else {
                    if let Some(inferred) = self.expr_ty(value).or_else(|| {
                        if matches!(value, Expr::List(_)) {
                            Some(Type::List(Box::new(Type::Int)))
                        } else {
                            None
                        }
                    }) {
                        self.local_env.insert(name.clone(), inferred);
                    }
                    out.push_str(&format!("{}{} {} = {};\n", pad, kw, name, val_str));
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
                out.push_str(&format!("{}switch ({}) {{\n", pad, self.fmt_expr(expr)));
                for arm in arms {
                    if arm.pat == MatchPat::Wildcard {
                        out.push_str(&format!("{}  default: {{\n", pad));
                    } else {
                        out.push_str(&format!("{}  case {}: {{\n", pad, fmt_pat(&arm.pat)));
                    }
                    let saved = self.local_env.clone();
                    for s in &arm.body {
                        self.fmt_stmt(s, indent + 2, out);
                    }
                    self.local_env = saved;
                    let ends_with_return = matches!(arm.body.last(), Some(Stmt::Return { .. }));
                    if !ends_with_return {
                        out.push_str(&format!("{}    break;\n", pad));
                    }
                    out.push_str(&format!("{}  }}\n", pad));
                }
                out.push_str(&format!("{}}}\n", pad));
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
                    "{}for (const {} of {}) {{\n",
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
                    "{}for (let {} = {}; {} < {}; {}++) {{\n",
                    pad,
                    var,
                    self.fmt_expr(start),
                    var,
                    self.fmt_expr(end),
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
                out.push_str(&format!(
                    "{}if (!({})) {{ throw new Error(\"assertion failed\"); }}\n",
                    pad,
                    self.fmt_expr(cond)
                ));
            }
            Stmt::AssertEq { left, right, .. } => {
                out.push_str(&format!(
                    "{}if (JSON.stringify({}) !== JSON.stringify({})) {{ throw new Error(\"assert_eq failed\"); }}\n",
                    pad,
                    self.fmt_expr(left),
                    self.fmt_expr(right)
                ));
            }
            Stmt::Expr { expr, .. } => {
                if matches!(expr, Expr::StructInit { .. }) {
                    out.push_str(&format!("{}({});\n", pad, self.fmt_expr(expr)));
                } else {
                    out.push_str(&format!("{}{};\n", pad, self.fmt_expr(expr)));
                }
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
        let pad = "  ".repeat(indent);
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
            Expr::Binary { .. } | Expr::Unary { .. } | Expr::StructInit { .. } => format!("({})", s),
            Expr::Int(v) if *v < 0 => format!("({})", s),
            Expr::Float(v) if *v < 0.0 => format!("({})", s),
            _ => s,
        }
    }

    fn fmt_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => v.to_string(),
            Expr::Float(v) => format_float(*v),
            Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Expr::Str(s) => format!("\"{}\"", escape_str(s)),
            Expr::Var(v) => v.clone(),
            Expr::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
            Expr::List(items) => {
                let inner: Vec<String> = items.iter().map(|e| self.fmt_expr(e)).collect();
                format!("[{}]", inner.join(", "))
            }
            Expr::StructInit { name, fields } => {
                let inner: Vec<String> = fields
                    .iter()
                    .map(|(fname, fval)| format!("{}: {}", fname, self.fmt_expr(fval)))
                    .collect();
                format!("{{ {} }} as {}", inner.join(", "), name)
            }
            Expr::FieldAccess { base, field } => format!("{}.{}", self.fmt_postfix(base), field),
            Expr::Index { base, index } => {
                format!("{}[{}]", self.fmt_postfix(base), self.fmt_expr(index))
            }
            Expr::Unary { op, expr: inner } => {
                let sym = match op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "!",
                };
                match inner.as_ref() {
                    Expr::Binary { .. } | Expr::Unary { .. } | Expr::StructInit { .. } => {
                        format!("{}({})", sym, self.fmt_expr(inner))
                    }
                    _ => format!("{}{}", sym, self.fmt_expr(inner)),
                }
            }
            Expr::Binary { op, left, right } => {
                if matches!(op, BinOp::Eq | BinOp::Ne)
                    && (self.expr_needs_deep_eq(left) || self.expr_needs_deep_eq(right))
                {
                    let op_str = if *op == BinOp::Eq { "===" } else { "!==" };
                    return format!(
                        "JSON.stringify({}) {} JSON.stringify({})",
                        self.fmt_expr(left),
                        op_str,
                        self.fmt_expr(right)
                    );
                }

                if *op == BinOp::IntDiv {
                    let l_str = if needs_parens(left, BinOp::Div, false) {
                        format!("({})", self.fmt_expr(left))
                    } else {
                        self.fmt_expr(left)
                    };
                    let r_str = if needs_parens(right, BinOp::Div, true) {
                        format!("({})", self.fmt_expr(right))
                    } else {
                        self.fmt_expr(right)
                    };
                    return format!("Math.trunc({} / {})", l_str, r_str);
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
                    BinOp::Eq => "===",
                    BinOp::Ne => "!==",
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
                let inner: Vec<String> = args.iter().map(|e| self.fmt_expr(e)).collect();
                format!("{}({})", func, inner.join(", "))
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e) => format!("{}.length", self.fmt_postfix(e)),
                Intrinsic::Min(a, b) => {
                    format!("Math.min({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Max(a, b) => {
                    format!("Math.max({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Abs(a) => format!("Math.abs({})", self.fmt_expr(a)),
                Intrinsic::Push { list, value } => {
                    format!("{}.push({})", self.fmt_postfix(list), self.fmt_expr(value))
                }
                Intrinsic::Print(args) => {
                    let inner: Vec<String> = args.iter().map(|e| self.fmt_expr(e)).collect();
                    format!("console.log({})", inner.join(", "))
                }
                Intrinsic::Contains { haystack, needle } => {
                    format!("{}.includes({})", self.fmt_postfix(haystack), self.fmt_expr(needle))
                }
                Intrinsic::Upper(e) => format!("{}.toUpperCase()", self.fmt_postfix(e)),
                Intrinsic::Lower(e) => format!("{}.toLowerCase()", self.fmt_postfix(e)),
                Intrinsic::ToStr(e) => format!("String({})", self.fmt_expr(e)),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum TsTokKind {
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
    EqEqEq,
    BangEq,
    BangEqEq,
    Lt,
    Le,
    Gt,
    Ge,
    PlusEq,
    MinusEq,
}

#[derive(Debug, Clone)]
struct TsTok {
    kind: TsTokKind,
    line: usize,
    col: usize,
}

fn lex_ts(src: &str) -> Result<Vec<TsTok>, Diagnostic> {
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
            tokens.push(TsTok {
                kind: TsTokKind::Comment(text),
                line,
                col: s_col,
            });
            continue;
        }
        if ch == '"' || ch == '\'' {
            let quote = ch;
            let s_line = line;
            let s_col = col;
            i += 1;
            col += 1;
            let mut raw = String::new();
            let mut closed = false;
            while i < chars.len() {
                let c = chars[i];
                if c == quote {
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
                    "typescript",
                    "unterminated string literal",
                    s_line,
                    s_col,
                ));
            }
            tokens.push(TsTok {
                kind: TsTokKind::Str(unescape_string(&raw)),
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
                let v = num_str.parse::<f64>().map_err(|_| {
                    Diagnostic::new("typescript", "invalid number literal", line, s_col)
                })?;
                tokens.push(TsTok {
                    kind: TsTokKind::Float(v),
                    line,
                    col: s_col,
                });
            } else {
                let v = num_str.parse::<i64>().map_err(|_| {
                    Diagnostic::new("typescript", "invalid integer literal", line, s_col)
                })?;
                tokens.push(TsTok {
                    kind: TsTokKind::Int(v),
                    line,
                    col: s_col,
                });
            }
            continue;
        }
        if ch.is_ascii_alphabetic() || ch == '_' || ch == '$' {
            let s_col = col;
            let start = i;
            while i < chars.len()
                && (chars[i].is_ascii_alphanumeric() || chars[i] == '_' || chars[i] == '$')
            {
                i += 1;
                col += 1;
            }
            let ident: String = chars[start..i].iter().collect();
            tokens.push(TsTok {
                kind: TsTokKind::Ident(ident),
                line,
                col: s_col,
            });
            continue;
        }

        let s_col = col;
        if i + 2 < chars.len() {
            let three = match (chars[i], chars[i + 1], chars[i + 2]) {
                ('=', '=', '=') => Some(TsTokKind::EqEqEq),
                ('!', '=', '=') => Some(TsTokKind::BangEqEq),
                _ => None,
            };
            if let Some(kind) = three {
                tokens.push(TsTok {
                    kind,
                    line,
                    col: s_col,
                });
                i += 3;
                col += 3;
                continue;
            }
        }
        if i + 1 < chars.len() {
            let two = match (chars[i], chars[i + 1]) {
                ('+', '+') => Some(TsTokKind::PlusPlus),
                ('&', '&') => Some(TsTokKind::AmpAmp),
                ('|', '|') => Some(TsTokKind::PipePipe),
                ('=', '=') => Some(TsTokKind::EqEq),
                ('!', '=') => Some(TsTokKind::BangEq),
                ('<', '=') => Some(TsTokKind::Le),
                ('>', '=') => Some(TsTokKind::Ge),
                ('+', '=') => Some(TsTokKind::PlusEq),
                ('-', '=') => Some(TsTokKind::MinusEq),
                _ => None,
            };
            if let Some(kind) = two {
                tokens.push(TsTok {
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
            '(' => TsTokKind::LParen,
            ')' => TsTokKind::RParen,
            '{' => TsTokKind::LBrace,
            '}' => TsTokKind::RBrace,
            '[' => TsTokKind::LBracket,
            ']' => TsTokKind::RBracket,
            ',' => TsTokKind::Comma,
            ';' => TsTokKind::Semi,
            ':' => TsTokKind::Colon,
            '.' => TsTokKind::Dot,
            '+' => TsTokKind::Plus,
            '-' => TsTokKind::Minus,
            '*' => TsTokKind::Star,
            '/' => TsTokKind::Slash,
            '%' => TsTokKind::Percent,
            '!' => TsTokKind::Bang,
            '=' => TsTokKind::Eq,
            '<' => TsTokKind::Lt,
            '>' => TsTokKind::Gt,
            other => {
                return Err(Diagnostic::new(
                    "typescript",
                    format!("unexpected character '{}'", other),
                    line,
                    s_col,
                ))
            }
        };
        tokens.push(TsTok {
            kind,
            line,
            col: s_col,
        });
        i += 1;
        col += 1;
    }

    Ok(tokens)
}

struct TsParser {
    tokens: Vec<TsTok>,
    pos: usize,
    known_structs: HashMap<String, Vec<String>>,
}

impl TsParser {
    fn peek(&self) -> Option<&TsTok> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&TsTokKind> {
        self.peek().map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<TsTok> {
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
        Err(Diagnostic::new("typescript", msg, line, col))
    }

    fn eat(&mut self, expected: &TsTokKind) -> bool {
        if self.peek_kind() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if matches!(self.peek_kind(), Some(TsTokKind::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &TsTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(expected) {
            Ok(())
        } else {
            self.err(format!("expected {}", label))
        }
    }

    fn expect_ident(&mut self) -> Result<String, Diagnostic> {
        match self.next() {
            Some(TsTok {
                kind: TsTokKind::Ident(s),
                ..
            }) => Ok(s),
            _ => self.err("expected identifier"),
        }
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut module = HubModule::new();
        let mut comments = Vec::new();

        while self.peek().is_some() {
            if let Some(TsTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.next();
                comments.push(c);
                continue;
            }
            if self.eat(&TsTokKind::Semi) {
                continue;
            }

            if matches!(self.peek_kind(), Some(TsTokKind::Ident(s)) if s == "main")
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(TsTokKind::LParen)
                )
            {
                self.next();
                self.next();
                self.expect(&TsTokKind::RParen, "')'")?;
                let _ = self.eat(&TsTokKind::Semi);
                continue;
            }

            let _ = self.eat_kw("export");
            let item_comments = std::mem::take(&mut comments);

            if self.eat_kw("enum") {
                let e = self.parse_ts_enum(item_comments)?;
                module.items.push(Item::Enum(e));
            } else if self.eat_kw("const") {
                // `export const Status = { Ok: 0, ... } as const;`
                let e = self.parse_const_enum(item_comments)?;
                module.items.push(Item::Enum(e));
            } else if self.eat_kw("type") {
                // Either `type Foo = { ... }` struct alias OR companion `export type Status = (typeof Status)[...];`
                let name = self.expect_ident()?;
                self.expect(&TsTokKind::Eq, "'=' after type")?;
                if matches!(self.peek_kind(), Some(TsTokKind::LBrace)) {
                    let s = self.parse_interface_body(name, item_comments)?;
                    self.known_structs.insert(
                        s.name.clone(),
                        s.fields.iter().map(|f| f.name.clone()).collect(),
                    );
                    module.items.push(Item::Struct(s));
                } else {
                    // Companion enum type alias -> skip until `;`
                    while !matches!(self.peek_kind(), Some(TsTokKind::Semi) | None) {
                        self.next();
                    }
                    let _ = self.eat(&TsTokKind::Semi);
                }
            } else if self.eat_kw("interface") {
                let name = self.expect_ident()?;
                let s = self.parse_interface_body(name, item_comments)?;
                self.known_structs.insert(
                    s.name.clone(),
                    s.fields.iter().map(|f| f.name.clone()).collect(),
                );
                module.items.push(Item::Struct(s));
            } else if self.eat_kw("function") {
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
                return self.err("expected 'interface', 'enum', 'const', or 'function' at top level");
            }
        }
        Ok(module)
    }

    fn parse_ts_enum(&mut self, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&TsTokKind::LBrace, "'{'")?;
        let mut variants = Vec::new();
        while !matches!(self.peek_kind(), Some(TsTokKind::RBrace) | None) {
            if let Some(TsTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            let vname = self.expect_ident()?;
            if self.eat(&TsTokKind::Eq) {
                let _ = self.parse_expr()?;
            }
            let _ = self.eat(&TsTokKind::Comma);
            variants.push(vname);
        }
        self.expect(&TsTokKind::RBrace, "'}'")?;
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_const_enum(&mut self, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&TsTokKind::Eq, "'='")?;
        self.expect(&TsTokKind::LBrace, "'{'")?;
        let mut variants = Vec::new();
        while !matches!(self.peek_kind(), Some(TsTokKind::RBrace) | None) {
            if let Some(TsTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            let vname = self.expect_ident()?;
            if self.eat(&TsTokKind::Colon) {
                let _ = self.parse_expr()?;
            }
            let _ = self.eat(&TsTokKind::Comma);
            variants.push(vname);
        }
        self.expect(&TsTokKind::RBrace, "'}'")?;
        if self.eat_kw("as") {
            let _ = self.expect_ident()?;
        }
        let _ = self.eat(&TsTokKind::Semi);
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_interface_body(
        &mut self,
        name: String,
        comments: Vec<String>,
    ) -> Result<StructDecl, Diagnostic> {
        self.expect(&TsTokKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), Some(TsTokKind::RBrace) | None) {
            if let Some(TsTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            let _ = self.eat_kw("readonly");
            let fname = self.expect_ident()?;
            self.expect(&TsTokKind::Colon, "':'")?;
            let fty = self.parse_type()?;
            let _ = self.eat(&TsTokKind::Semi);
            let _ = self.eat(&TsTokKind::Comma);
            fields.push(Field {
                id: 0,
                name: fname,
                ty: fty,
                meta: Metadata::new(),
            });
        }
        self.expect(&TsTokKind::RBrace, "'}'")?;
        let _ = self.eat(&TsTokKind::Semi);
        Ok(StructDecl {
            id: 0,
            name,
            fields,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_fn(&mut self, comments: Vec<String>) -> Result<FnDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&TsTokKind::LParen, "'('")?;
        let mut params = Vec::new();
        while !matches!(self.peek_kind(), Some(TsTokKind::RParen) | None) {
            let pname = self.expect_ident()?;
            let pty = if self.eat(&TsTokKind::Colon) {
                self.parse_type()?
            } else {
                Type::Int
            };
            params.push(Param {
                id: 0,
                name: pname,
                ty: pty,
                meta: Metadata::new(),
            });
            if !self.eat(&TsTokKind::Comma) {
                break;
            }
        }
        self.expect(&TsTokKind::RParen, "')'")?;
        let ret_ty = if self.eat(&TsTokKind::Colon) {
            self.parse_type()?
        } else {
            Type::Void
        };
        let body = self.parse_block()?;
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
        let ident = self.expect_ident()?;
        let mut base = match ident.as_str() {
            "number" => Type::Int,
            "boolean" => Type::Bool,
            "string" => Type::Str,
            "void" => Type::Void,
            "Array" | "ReadonlyArray" => {
                self.expect(&TsTokKind::Lt, "'<'")?;
                let inner = self.parse_type()?;
                self.expect(&TsTokKind::Gt, "'>'")?;
                Type::list(inner)
            }
            other => Type::Named(other.to_string()),
        };
        while self.eat(&TsTokKind::LBracket) {
            self.expect(&TsTokKind::RBracket, "']'")?;
            base = Type::list(base);
        }
        Ok(base)
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        self.expect(&TsTokKind::LBrace, "'{'")?;
        let mut stmts = Vec::new();
        while !matches!(self.peek_kind(), Some(TsTokKind::RBrace) | None) {
            if let Some(TsTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.next();
                stmts.push(Stmt::Comment { id: 0, text: c });
                continue;
            }
            if self.eat(&TsTokKind::Semi) {
                continue;
            }
            stmts.push(self.parse_stmt()?);
        }
        self.expect(&TsTokKind::RBrace, "'}'")?;
        Ok(stmts)
    }

    fn parse_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        if let Some(TsTokKind::Comment(c)) = self.peek_kind().cloned() {
            self.next();
            return Ok(Stmt::Comment { id: 0, text: c });
        }
        if self.eat_kw("const") || self.eat_kw("let") || self.eat_kw("var") {
            let prev_tok = &self.tokens[self.pos - 1].kind;
            let mutable = matches!(prev_tok, TsTokKind::Ident(s) if s != "const");
            let name = self.expect_ident()?;
            let ty = if self.eat(&TsTokKind::Colon) {
                Some(self.parse_type()?)
            } else {
                None
            };
            self.expect(&TsTokKind::Eq, "'='")?;
            let value = self.parse_expr()?;
            let _ = self.eat(&TsTokKind::Semi);
            let mut meta = Metadata::new();
            if mutable {
                meta.insert("explicit_mut".to_string(), "true".to_string());
            }
            return Ok(Stmt::Let {
                id: 0,
                name,
                mutable,
                ty,
                value,
                meta,
            });
        }
        if self.eat_kw("if") {
            return self.parse_if();
        }
        if self.eat_kw("switch") {
            return self.parse_switch();
        }
        if self.eat_kw("while") {
            self.expect(&TsTokKind::LParen, "'('")?;
            let cond = self.parse_expr()?;
            self.expect(&TsTokKind::RParen, "')'")?;
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
            let _ = self.eat(&TsTokKind::Semi);
            return Ok(Stmt::Break { id: 0 });
        }
        if self.eat_kw("continue") {
            let _ = self.eat(&TsTokKind::Semi);
            return Ok(Stmt::Continue { id: 0 });
        }
        if self.eat_kw("return") {
            if self.eat(&TsTokKind::Semi) || matches!(self.peek_kind(), Some(TsTokKind::RBrace)) {
                return Ok(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                });
            }
            let val = self.parse_expr()?;
            let _ = self.eat(&TsTokKind::Semi);
            return Ok(Stmt::Return {
                id: 0,
                value: Some(val),
                meta: Metadata::new(),
            });
        }

        if matches!(self.peek_kind(), Some(TsTokKind::Ident(s)) if s == "console")
            && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&TsTokKind::Dot)
            && matches!(
                self.tokens.get(self.pos + 2).map(|t| &t.kind),
                Some(TsTokKind::Ident(m)) if m == "assert"
            )
            && self.tokens.get(self.pos + 3).map(|t| &t.kind) == Some(&TsTokKind::LParen)
        {
            self.pos += 4;
            let mut args = self.parse_expr_list(&TsTokKind::RParen)?;
            let _ = self.eat(&TsTokKind::Semi);
            if args.is_empty() {
                return self.err("console.assert(...) requires a condition");
            }
            return Ok(Stmt::Assert {
                id: 0,
                cond: args.remove(0),
                meta: Metadata::new(),
            });
        }

        let expr = self.parse_expr()?;
        if let Some(op) = match self.peek_kind() {
            Some(TsTokKind::Eq) => Some(AssignOp::Set),
            Some(TsTokKind::PlusEq) => Some(AssignOp::AddAssign),
            Some(TsTokKind::MinusEq) => Some(AssignOp::SubAssign),
            _ => None,
        } {
            self.next();
            let target = ts_expr_to_target(expr)?;
            let value = self.parse_expr()?;
            let _ = self.eat(&TsTokKind::Semi);
            Ok(Stmt::Assign {
                id: 0,
                target,
                op,
                value,
                meta: Metadata::new(),
            })
        } else {
            let _ = self.eat(&TsTokKind::Semi);
            Ok(Stmt::Expr {
                id: 0,
                expr,
                meta: Metadata::new(),
            })
        }
    }

    fn parse_if(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&TsTokKind::LParen, "'('")?;
        let cond = self.parse_expr()?;
        self.expect(&TsTokKind::RParen, "')'")?;
        if matches!(self.peek_kind(), Some(TsTokKind::LBrace))
            && matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(TsTokKind::Ident(s)) if s == "throw"
            )
        {
            // `{ throw new Error("..."); }` assertion lowering
            self.expect(&TsTokKind::LBrace, "'{'")?;
            let mut depth = 1usize;
            while depth > 0 {
                match self.next().map(|t| t.kind) {
                    Some(TsTokKind::LBrace) => depth += 1,
                    Some(TsTokKind::RBrace) => depth -= 1,
                    Some(_) => {}
                    None => return self.err("unclosed '{' in throw block"),
                }
            }
            if let Expr::Binary {
                op: BinOp::Ne,
                left,
                right,
            } = cond
            {
                return Ok(Stmt::AssertEq {
                    id: 0,
                    left: *left,
                    right: *right,
                    meta: Metadata::new(),
                });
            }
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
            return Ok(Stmt::Assert {
                id: 0,
                cond,
                meta: Metadata::new(),
            });
        }
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

    fn parse_switch(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&TsTokKind::LParen, "'('")?;
        let expr = self.parse_expr()?;
        self.expect(&TsTokKind::RParen, "')'")?;
        self.expect(&TsTokKind::LBrace, "'{'")?;
        let mut arms = Vec::new();

        while !matches!(self.peek_kind(), Some(TsTokKind::RBrace) | None) {
            if matches!(self.peek_kind(), Some(TsTokKind::Comment(_))) {
                self.next();
                continue;
            }
            let pat = if self.eat_kw("default") {
                self.expect(&TsTokKind::Colon, "':'")?;
                MatchPat::Wildcard
            } else if self.eat_kw("case") {
                let pexpr = self.parse_expr()?;
                self.expect(&TsTokKind::Colon, "':'")?;
                match pexpr {
                    Expr::FieldAccess { base, field } => {
                        if let Expr::Var(ename) = *base {
                            MatchPat::EnumVariant {
                                enum_name: ename,
                                variant: field,
                            }
                        } else {
                            return self.err("invalid case pattern");
                        }
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
                    _ => return self.err("unsupported TypeScript switch case pattern"),
                }
            } else {
                return self.err("expected 'case' or 'default' in switch");
            };

            let mut body = if matches!(self.peek_kind(), Some(TsTokKind::LBrace)) {
                self.parse_block()?
            } else {
                let mut list = Vec::new();
                while !matches!(self.peek_kind(), Some(TsTokKind::RBrace) | None)
                    && !matches!(
                        self.peek_kind(),
                        Some(TsTokKind::Ident(s)) if s == "case" || s == "default"
                    )
                {
                    list.push(self.parse_stmt()?);
                }
                list
            };

            // Strip trailing fallthrough-prevention `break;` from switch case arm
            if matches!(body.last(), Some(Stmt::Break { .. })) {
                body.pop();
            }
            arms.push(MatchArm { pat, body });
        }

        self.expect(&TsTokKind::RBrace, "'}'")?;
        Ok(Stmt::Match {
            id: 0,
            expr,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_for(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&TsTokKind::LParen, "'(' after for")?;
        let _ = self.eat_kw("const") || self.eat_kw("let") || self.eat_kw("var");
        let var = self.expect_ident()?;

        if self.eat_kw("of") {
            let iter = self.parse_expr()?;
            self.expect(&TsTokKind::RParen, "')'")?;
            let body = self.parse_block()?;
            return Ok(Stmt::ForEach {
                id: 0,
                var,
                iter,
                body,
                meta: Metadata::new(),
            });
        }

        if self.eat(&TsTokKind::Colon) {
            let _ = self.parse_type()?;
        }
        self.expect(&TsTokKind::Eq, "'=' in for range header")?;
        let start = self.parse_expr()?;
        self.expect(&TsTokKind::Semi, "';' in for range header")?;

        let cond_var = self.expect_ident()?;
        if cond_var != var {
            return self.err("for-loop condition variable must match loop variable");
        }
        self.expect(&TsTokKind::Lt, "'<' in for range header")?;
        let end = self.parse_expr()?;
        self.expect(&TsTokKind::Semi, "';' after for condition")?;

        if self.eat(&TsTokKind::PlusPlus) {
            let _ = self.expect_ident()?;
        } else {
            let _ = self.expect_ident()?;
            if !self.eat(&TsTokKind::PlusPlus)
                && (self.eat(&TsTokKind::PlusEq) || self.eat(&TsTokKind::Eq))
            {
                let _ = self.parse_expr()?;
            }
        }
        self.expect(&TsTokKind::RParen, "')' after for header")?;
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
        while self.eat(&TsTokKind::PipePipe) {
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
        while self.eat(&TsTokKind::AmpAmp) {
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
                Some(TsTokKind::EqEq) | Some(TsTokKind::EqEqEq) => Some(BinOp::Eq),
                Some(TsTokKind::BangEq) | Some(TsTokKind::BangEqEq) => Some(BinOp::Ne),
                Some(TsTokKind::Lt) => Some(BinOp::Lt),
                Some(TsTokKind::Le) => Some(BinOp::Le),
                Some(TsTokKind::Gt) => Some(BinOp::Gt),
                Some(TsTokKind::Ge) => Some(BinOp::Ge),
                _ => None,
            };
            if let Some(op) = op {
                self.next();
                let right = self.parse_add()?;
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    if let (
                        Expr::Call {
                            func: lf,
                            args: largs,
                        },
                        Expr::Call {
                            func: rf,
                            args: rargs,
                        },
                    ) = (&left, &right)
                    {
                        if lf == "__json_stringify"
                            && rf == "__json_stringify"
                            && largs.len() == 1
                            && rargs.len() == 1
                        {
                            left = Expr::Binary {
                                op,
                                left: Box::new(largs[0].clone()),
                                right: Box::new(rargs[0].clone()),
                            };
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
                Some(TsTokKind::Plus) => Some(BinOp::Add),
                Some(TsTokKind::Minus) => Some(BinOp::Sub),
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
        let mut left = self.parse_as()?;
        loop {
            let op = match self.peek_kind() {
                Some(TsTokKind::Star) => Some(BinOp::Mul),
                Some(TsTokKind::Slash) => Some(BinOp::Div),
                Some(TsTokKind::Percent) => Some(BinOp::Mod),
                _ => None,
            };
            if let Some(op) = op {
                self.next();
                let right = self.parse_as()?;
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

    fn parse_as(&mut self) -> Result<Expr, Diagnostic> {
        let mut expr = self.parse_unary()?;
        while self.eat_kw("as") {
            let t = self.parse_type()?;
            if let (Type::Named(new_name), Expr::StructInit { name, .. }) = (t, &mut expr) {
                *name = new_name;
            }
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<Expr, Diagnostic> {
        if self.eat(&TsTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        if self.eat(&TsTokKind::Bang) {
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
            if self.eat(&TsTokKind::Dot) {
                let member = self.expect_ident()?;
                if self.eat(&TsTokKind::LParen) {
                    let mut args = self.parse_expr_list(&TsTokKind::RParen)?;
                    base = match (&base, member.as_str(), args.len()) {
                        (Expr::Var(ns), "min", 2) if ns == "Math" => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            Expr::intrinsic(Intrinsic::Min(a, b))
                        }
                        (Expr::Var(ns), "max", 2) if ns == "Math" => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            Expr::intrinsic(Intrinsic::Max(a, b))
                        }
                        (Expr::Var(ns), "abs", 1) if ns == "Math" => {
                            Expr::intrinsic(Intrinsic::Abs(args.pop().unwrap()))
                        }
                        (Expr::Var(ns), "trunc" | "floor", 1) if ns == "Math" => {
                            let inner = args.pop().unwrap();
                            if let Expr::Binary {
                                op: BinOp::Div,
                                left,
                                right,
                            } = inner
                            {
                                Expr::Binary {
                                    op: BinOp::IntDiv,
                                    left,
                                    right,
                                }
                            } else {
                                inner
                            }
                        }
                        (Expr::Var(ns), "log", _) if ns == "console" => {
                            Expr::intrinsic(Intrinsic::Print(args))
                        }
                        (Expr::Var(ns), "stringify", 1) if ns == "JSON" => Expr::Call {
                            func: "__json_stringify".to_string(),
                            args,
                        },
                        (_, "push", 1) => Expr::intrinsic(Intrinsic::Push {
                            list: base,
                            value: args.pop().unwrap(),
                        }),
                        (_, "includes", 1) => Expr::intrinsic(Intrinsic::Contains {
                            haystack: base,
                            needle: args.pop().unwrap(),
                        }),
                        (_, "toUpperCase", 0) => Expr::intrinsic(Intrinsic::Upper(base)),
                        (_, "toLowerCase", 0) => Expr::intrinsic(Intrinsic::Lower(base)),
                        _ => {
                            return self.err(format!(
                                "unsupported TypeScript method '.{}(...)'",
                                member
                            ))
                        }
                    };
                } else if member == "length" {
                    base = Expr::intrinsic(Intrinsic::Len(base));
                } else {
                    base = Expr::FieldAccess {
                        base: Box::new(base),
                        field: member,
                    };
                }
            } else if self.eat(&TsTokKind::LBracket) {
                let idx = self.parse_expr()?;
                self.expect(&TsTokKind::RBracket, "']'")?;
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
            Some(TsTokKind::Int(v)) => {
                self.next();
                Ok(Expr::Int(v))
            }
            Some(TsTokKind::Float(v)) => {
                self.next();
                Ok(Expr::Float(v))
            }
            Some(TsTokKind::Str(s)) => {
                self.next();
                Ok(Expr::Str(s))
            }
            Some(TsTokKind::LParen) => {
                self.next();
                let e = self.parse_expr()?;
                self.expect(&TsTokKind::RParen, "')'")?;
                Ok(e)
            }
            Some(TsTokKind::LBracket) => {
                self.next();
                let items = self.parse_expr_list(&TsTokKind::RBracket)?;
                Ok(Expr::List(items))
            }
            Some(TsTokKind::LBrace) => {
                self.next();
                let mut fields = Vec::new();
                while !matches!(self.peek_kind(), Some(TsTokKind::RBrace) | None) {
                    let fname = self.expect_ident()?;
                    let fval = if self.eat(&TsTokKind::Colon) {
                        self.parse_expr()?
                    } else {
                        Expr::Var(fname.clone())
                    };
                    fields.push((fname, fval));
                    if !self.eat(&TsTokKind::Comma) {
                        break;
                    }
                }
                self.expect(&TsTokKind::RBrace, "'}'")?;
                let inferred_name = self.infer_struct_by_fields(&fields);
                Ok(Expr::StructInit {
                    name: inferred_name,
                    fields,
                })
            }
            Some(TsTokKind::Ident(ident)) => {
                self.next();
                if ident == "true" {
                    return Ok(Expr::Bool(true));
                }
                if ident == "false" {
                    return Ok(Expr::Bool(false));
                }
                if self.eat(&TsTokKind::LParen) {
                    let mut args = self.parse_expr_list(&TsTokKind::RParen)?;
                    if ident == "String" && args.len() == 1 {
                        return Ok(Expr::intrinsic(Intrinsic::ToStr(args.pop().unwrap())));
                    }
                    return Ok(Expr::Call { func: ident, args });
                }
                Ok(Expr::Var(ident))
            }
            _ => self.err("expected TypeScript expression"),
        }
    }

    fn infer_struct_by_fields(&self, fields: &[(String, Expr)]) -> String {
        let fset: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        for (sname, known_fields) in &self.known_structs {
            if known_fields.len() == fset.len()
                && known_fields.iter().all(|kf| fset.contains(&kf.as_str()))
            {
                return sname.clone();
            }
        }
        "AnonymousStruct".to_string()
    }

    fn parse_expr_list(&mut self, closing: &TsTokKind) -> Result<Vec<Expr>, Diagnostic> {
        let mut items = Vec::new();
        while self.peek_kind() != Some(closing) && self.peek().is_some() {
            items.push(self.parse_expr()?);
            if !self.eat(&TsTokKind::Comma) {
                break;
            }
        }
        self.expect(closing, "closing ')' or ']'")?;
        Ok(items)
    }
}

fn ts_expr_to_target(expr: Expr) -> Result<AssignTarget, Diagnostic> {
    match expr {
        Expr::Var(v) => Ok(AssignTarget::Var(v)),
        Expr::FieldAccess { base, field } => {
            if let Expr::Var(b) = *base {
                Ok(AssignTarget::Field { base: b, field })
            } else {
                Err(Diagnostic::new(
                    "typescript",
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
                    "typescript",
                    "nested index assignment not supported",
                    1,
                    1,
                ))
            }
        }
        _ => Err(Diagnostic::new(
            "typescript",
            "invalid assignment target",
            1,
            1,
        )),
    }
}

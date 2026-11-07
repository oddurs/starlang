use std::collections::{HashMap, HashSet};

use crate::hub::{
    AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl, HubModule, Intrinsic,
    Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl, Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct SwiftLens;

impl LanguageLens for SwiftLens {
    fn id(&self) -> SpokeId {
        SpokeId::Swift
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut struct_fields: HashMap<String, Vec<String>> = HashMap::new();
        for item in &hub.items {
            if let Item::Struct(s) = item {
                struct_fields.insert(
                    s.name.clone(),
                    s.fields.iter().map(|f| f.name.clone()).collect(),
                );
            }
        }

        let emitter = SwiftEmitter { struct_fields };
        let mut out = String::new();
        for (idx, item) in hub.items.iter().enumerate() {
            if idx > 0 {
                out.push('\n');
            }
            match item {
                Item::Struct(s) => emitter.fmt_struct(s, &mut out),
                Item::Enum(e) => emitter.fmt_enum(e, &mut out),
                Item::Function(f) => emitter.fmt_fn(f, &mut out),
                Item::Test(t) => emitter.fmt_test(t, &mut out),
            }
        }
        if hub.has_main() {
            out.push_str("\nmain()\n");
        }
        out
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_swift(source)?;
        let mut known_structs: HashSet<String> = HashSet::new();
        let mut known_enums: HashSet<String> = HashSet::new();
        for item in &prev_hub.items {
            match item {
                Item::Struct(s) => {
                    known_structs.insert(s.name.clone());
                }
                Item::Enum(e) => {
                    known_enums.insert(e.name.clone());
                }
                _ => {}
            }
        }
        // Pre-scan module tokens for struct/enum declarations so forward references work cleanly.
        for win in tokens.windows(2) {
            match (&win[0].kind, &win[1].kind) {
                (SwiftTokKind::Ident(kw), SwiftTokKind::Ident(name)) if kw == "struct" => {
                    known_structs.insert(name.clone());
                }
                (SwiftTokKind::Ident(kw), SwiftTokKind::Ident(name)) if kw == "enum" => {
                    known_enums.insert(name.clone());
                }
                _ => {}
            }
        }

        let mut parser = SwiftParser {
            tokens,
            pos: 0,
            known_structs,
            known_enums,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Swift))
    }
}

struct SwiftEmitter {
    struct_fields: HashMap<String, Vec<String>>,
}

impl SwiftEmitter {
    fn fmt_type(ty: &Type) -> String {
        match ty {
            Type::Int => "Int".to_string(),
            Type::Float => "Double".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Str => "String".to_string(),
            Type::Void => "Void".to_string(),
            Type::List(inner) => format!("[{}]", Self::fmt_type(inner)),
            Type::Named(name) => name.clone(),
        }
    }

    fn fmt_struct(&self, s: &StructDecl, out: &mut String) {
        for c in &s.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("struct {}: Equatable {{\n", s.name));
        for f in &s.fields {
            out.push_str(&format!("    var {}: {}\n", f.name, Self::fmt_type(&f.ty)));
        }
        out.push_str("}\n");
    }

    fn fmt_enum(&self, e: &EnumDecl, out: &mut String) {
        for c in &e.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("enum {}: Equatable {{\n", e.name));
        for v in &e.variants {
            out.push_str(&format!("    case {}\n", v));
        }
        out.push_str("}\n");
    }

    fn fmt_fn(&self, f: &FnDecl, out: &mut String) {
        for c in &f.comments {
            out.push_str(&format!("// {}\n", c));
        }
        let params_str: Vec<String> = f
            .params
            .iter()
            .map(|p| format!("_ {}: {}", p.name, Self::fmt_type(&p.ty)))
            .collect();
        if f.ret_ty == Type::Void {
            out.push_str(&format!("func {}({}) {{\n", f.name, params_str.join(", ")));
        } else {
            out.push_str(&format!(
                "func {}({}) -> {} {{\n",
                f.name,
                params_str.join(", "),
                Self::fmt_type(&f.ret_ty)
            ));
        }

        let mut mutated = HashSet::new();
        collect_mutated(&f.body, &mut mutated);
        for p in &f.params {
            if mutated.contains(&p.name) {
                out.push_str(&format!("    var {} = {}\n", p.name, p.name));
            }
        }

        for stmt in &f.body {
            self.fmt_stmt(stmt, 1, out);
        }
        if f.ret_ty != Type::Void && !stmts_guaranteed_return(&f.body) {
            out.push_str("    fatalError(\"unreachable\")\n");
        }
        out.push_str("}\n");
    }

    fn fmt_test(&self, t: &TestDecl, out: &mut String) {
        for c in &t.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("func test_{}() {{\n", t.name));
        for stmt in &t.body {
            self.fmt_stmt(stmt, 1, out);
        }
        out.push_str("}\n");
    }

    fn fmt_pat(pat: &MatchPat) -> String {
        match pat {
            MatchPat::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
            MatchPat::Int(v) => v.to_string(),
            MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
            MatchPat::Wildcard => "default".to_string(),
        }
    }

    fn fmt_stmt(&self, stmt: &Stmt, indent: usize, out: &mut String) {
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
                let kw = if *mutable { "var" } else { "let" };
                if let Some(t) = ty {
                    out.push_str(&format!(
                        "{}{} {}: {} = {}\n",
                        pad,
                        kw,
                        name,
                        Self::fmt_type(t),
                        self.fmt_expr(value)
                    ));
                } else if matches!(value, Expr::List(items) if items.is_empty()) {
                    out.push_str(&format!("{}{} {}: [Int] = []\n", pad, kw, name));
                } else {
                    out.push_str(&format!(
                        "{}{} {} = {}\n",
                        pad,
                        kw,
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
                        format!("{}[{}]", base, self.fmt_expr(index))
                    }
                };
                out.push_str(&format!(
                    "{}{} {} {}\n",
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
                out.push_str(&format!("{}switch {} {{\n", pad, self.fmt_expr(expr)));
                let mut has_wildcard = false;
                let needs_default = arms.is_empty()
                    || arms
                        .iter()
                        .any(|a| matches!(a.pat, MatchPat::Int(_) | MatchPat::Str(_)));
                for arm in arms {
                    if arm.pat == MatchPat::Wildcard {
                        has_wildcard = true;
                        out.push_str(&format!("{}default:\n", pad));
                    } else {
                        out.push_str(&format!("{}case {}:\n", pad, Self::fmt_pat(&arm.pat)));
                    }
                    for s in &arm.body {
                        self.fmt_stmt(s, indent + 1, out);
                    }
                    let has_exec = arm
                        .body
                        .iter()
                        .any(|s| !matches!(s, Stmt::Comment { .. }));
                    if !has_exec {
                        out.push_str(&format!("{}    break\n", pad));
                    }
                }
                if !has_wildcard && needs_default {
                    out.push_str(&format!("{}default:\n", pad));
                    out.push_str(&format!("{}    fatalError(\"unreachable\")\n", pad));
                }
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::While { cond, body, .. } => {
                out.push_str(&format!("{}while {} {{\n", pad, self.fmt_expr(cond)));
                for s in body {
                    self.fmt_stmt(s, indent + 1, out);
                }
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let mut body_mut = HashSet::new();
                collect_mutated(body, &mut body_mut);
                let var_kw = if body_mut.contains(var) { "var " } else { "" };
                out.push_str(&format!(
                    "{}for {}{} in {} {{\n",
                    pad,
                    var_kw,
                    var,
                    self.fmt_expr(iter)
                ));
                for s in body {
                    self.fmt_stmt(s, indent + 1, out);
                }
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                let mut body_mut = HashSet::new();
                collect_mutated(body, &mut body_mut);
                let var_kw = if body_mut.contains(var) { "var " } else { "" };
                out.push_str(&format!(
                    "{}for {}{} in stride(from: {}, to: {}, by: 1) {{\n",
                    pad,
                    var_kw,
                    var,
                    self.fmt_expr(start),
                    self.fmt_expr(end)
                ));
                for s in body {
                    self.fmt_stmt(s, indent + 1, out);
                }
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::Break { .. } => out.push_str(&format!("{}break\n", pad)),
            Stmt::Continue { .. } => out.push_str(&format!("{}continue\n", pad)),
            Stmt::Return { value, .. } => match value {
                Some(v) => out.push_str(&format!("{}return {}\n", pad, self.fmt_expr(v))),
                None => out.push_str(&format!("{}return\n", pad)),
            },
            Stmt::Assert { cond, .. } => {
                out.push_str(&format!("{}assert({})\n", pad, self.fmt_expr(cond)));
            }
            Stmt::AssertEq { left, right, .. } => {
                let both_empty = matches!(left, Expr::List(l) if l.is_empty())
                    && matches!(right, Expr::List(r) if r.is_empty());
                if both_empty {
                    out.push_str(&format!("{}assert(([] as [Int]) == [])\n", pad));
                } else {
                    let l_s = if matches!(left, Expr::Binary { .. }) {
                        format!("({})", self.fmt_expr(left))
                    } else {
                        self.fmt_expr(left)
                    };
                    let r_s = if matches!(right, Expr::Binary { .. }) {
                        format!("({})", self.fmt_expr(right))
                    } else {
                        self.fmt_expr(right)
                    };
                    out.push_str(&format!("{}assert({} == {})\n", pad, l_s, r_s));
                }
            }
            Stmt::Expr { expr, .. } => {
                out.push_str(&format!("{}{}\n", pad, self.fmt_expr(expr)));
            }
        }
    }

    fn fmt_if_chain(
        &self,
        cond: &Expr,
        then_body: &[Stmt],
        else_body: &[Stmt],
        indent: usize,
        is_first: bool,
        out: &mut String,
    ) {
        let pad = "    ".repeat(indent);
        if is_first {
            out.push_str(&format!("{}if {} {{\n", pad, self.fmt_expr(cond)));
        } else {
            out.push_str(&format!(" else if {} {{\n", self.fmt_expr(cond)));
        }
        for s in then_body {
            self.fmt_stmt(s, indent + 1, out);
        }
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
            for s in else_body {
                self.fmt_stmt(s, indent + 1, out);
            }
            out.push_str(&format!("{}}}\n", pad));
        }
    }

    fn fmt_postfix(&self, expr: &Expr) -> String {
        match expr {
            Expr::Binary { .. } | Expr::Unary { .. } => format!("({})", self.fmt_expr(expr)),
            Expr::Int(v) if *v < 0 => format!("({})", v),
            Expr::Float(v) if *v < 0.0 => format!("({})", format_float(*v)),
            _ => self.fmt_expr(expr),
        }
    }

    fn fmt_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => v.to_string(),
            Expr::Float(v) => format_float(*v),
            Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Expr::Str(s) => format!("\"{}\"", escape_str(s)),
            Expr::Var(name) => name.clone(),
            Expr::List(items) => {
                let inner: Vec<String> = items.iter().map(|e| self.fmt_expr(e)).collect();
                format!("[{}]", inner.join(", "))
            }
            Expr::StructInit { name, fields } => {
                let ordered: Vec<(String, String)> =
                    if let Some(decl_order) = self.struct_fields.get(name) {
                        let mut out_f = Vec::with_capacity(fields.len());
                        for df in decl_order {
                            if let Some((_, val)) = fields.iter().find(|(k, _)| k == df) {
                                out_f.push((df.clone(), self.fmt_expr(val)));
                            }
                        }
                        for (k, val) in fields {
                            if !decl_order.contains(k) {
                                out_f.push((k.clone(), self.fmt_expr(val)));
                            }
                        }
                        out_f
                    } else {
                        fields
                            .iter()
                            .map(|(k, v)| (k.clone(), self.fmt_expr(v)))
                            .collect()
                    };
                let parts: Vec<String> = ordered
                    .into_iter()
                    .map(|(k, v)| format!("{}: {}", k, v))
                    .collect();
                format!("{}({})", name, parts.join(", "))
            }
            Expr::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
            Expr::FieldAccess { base, field } => {
                format!("{}.{}", self.fmt_postfix(base), field)
            }
            Expr::Index { base, index } => {
                format!("{}[{}]", self.fmt_postfix(base), self.fmt_expr(index))
            }
            Expr::Unary { op, expr: inner } => {
                let inner_s = if matches!(inner.as_ref(), Expr::Binary { .. } | Expr::Unary { .. })
                {
                    format!("({})", self.fmt_expr(inner))
                } else if matches!(inner.as_ref(), Expr::Int(v) if *v < 0)
                    || matches!(inner.as_ref(), Expr::Float(v) if *v < 0.0)
                {
                    format!("({})", self.fmt_expr(inner))
                } else {
                    self.fmt_expr(inner)
                };
                match op {
                    UnaryOp::Neg => format!("-{}", inner_s),
                    UnaryOp::Not => format!("!{}", inner_s),
                }
            }
            Expr::Binary { op, left, right } => {
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
                let a: Vec<String> = args.iter().map(|e| self.fmt_expr(e)).collect();
                format!("{}({})", func, a.join(", "))
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e) => format!("{}.count", self.fmt_postfix(e)),
                Intrinsic::Min(a, b) => format!("min({}, {})", self.fmt_expr(a), self.fmt_expr(b)),
                Intrinsic::Max(a, b) => format!("max({}, {})", self.fmt_expr(a), self.fmt_expr(b)),
                Intrinsic::Abs(a) => format!("abs({})", self.fmt_expr(a)),
                Intrinsic::Push { list, value } => {
                    format!("{}.append({})", self.fmt_postfix(list), self.fmt_expr(value))
                }
                Intrinsic::Print(args) => {
                    let a: Vec<String> = args.iter().map(|e| self.fmt_expr(e)).collect();
                    format!("print({})", a.join(", "))
                }
                Intrinsic::Contains { haystack, needle } => {
                    format!(
                        "{}.contains({})",
                        self.fmt_postfix(haystack),
                        self.fmt_expr(needle)
                    )
                }
                Intrinsic::Upper(e) => format!("{}.uppercased()", self.fmt_postfix(e)),
                Intrinsic::Lower(e) => format!("{}.lowercased()", self.fmt_postfix(e)),
                Intrinsic::ToStr(e) => format!("String({})", self.fmt_expr(e)),
            },
        }
    }
}

fn stmts_guaranteed_return(stmts: &[Stmt]) -> bool {
    let Some(last) = stmts
        .iter()
        .rev()
        .find(|s| !matches!(s, Stmt::Comment { .. }))
    else {
        return false;
    };
    match last {
        Stmt::Return { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            !else_body.is_empty()
                && stmts_guaranteed_return(then_body)
                && stmts_guaranteed_return(else_body)
        }
        Stmt::Match { arms, .. } => {
            !arms.is_empty() && arms.iter().all(|a| stmts_guaranteed_return(&a.body))
        }
        _ => false,
    }
}

fn collect_mutated(stmts: &[Stmt], out: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Assign { target, value, .. } => {
                out.insert(target.root_var().to_string());
                collect_mutated_expr(value, out);
            }
            Stmt::Let { value, .. } | Stmt::Expr { expr: value, .. } => {
                collect_mutated_expr(value, out);
            }
            Stmt::Return {
                value: Some(v), ..
            } => collect_mutated_expr(v, out),
            Stmt::Assert { cond, .. } => collect_mutated_expr(cond, out),
            Stmt::AssertEq { left, right, .. } => {
                collect_mutated_expr(left, out);
                collect_mutated_expr(right, out);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                collect_mutated_expr(cond, out);
                collect_mutated(then_body, out);
                collect_mutated(else_body, out);
            }
            Stmt::Match { expr, arms, .. } => {
                collect_mutated_expr(expr, out);
                for arm in arms {
                    collect_mutated(&arm.body, out);
                }
            }
            Stmt::While { cond, body, .. } => {
                collect_mutated_expr(cond, out);
                collect_mutated(body, out);
            }
            Stmt::ForEach { iter, body, .. } => {
                collect_mutated_expr(iter, out);
                collect_mutated(body, out);
            }
            Stmt::ForRange {
                start, end, body, ..
            } => {
                collect_mutated_expr(start, out);
                collect_mutated_expr(end, out);
                collect_mutated(body, out);
            }
            _ => {}
        }
    }
}

fn collect_mutated_expr(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Push { list, value } => {
                if let Expr::Var(v) = list {
                    out.insert(v.clone());
                }
                collect_mutated_expr(list, out);
                collect_mutated_expr(value, out);
            }
            Intrinsic::Len(a)
            | Intrinsic::Abs(a)
            | Intrinsic::Upper(a)
            | Intrinsic::Lower(a)
            | Intrinsic::ToStr(a) => collect_mutated_expr(a, out),
            Intrinsic::Min(a, b)
            | Intrinsic::Max(a, b)
            | Intrinsic::Contains {
                haystack: a,
                needle: b,
            } => {
                collect_mutated_expr(a, out);
                collect_mutated_expr(b, out);
            }
            Intrinsic::Print(args) => {
                for a in args {
                    collect_mutated_expr(a, out);
                }
            }
        },
        Expr::List(items) | Expr::Call { args: items, .. } => {
            for e in items {
                collect_mutated_expr(e, out);
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, v) in fields {
                collect_mutated_expr(v, out);
            }
        }
        Expr::FieldAccess { base, .. } | Expr::Unary { expr: base, .. } => {
            collect_mutated_expr(base, out);
        }
        Expr::Index { base, index } => {
            collect_mutated_expr(base, out);
            collect_mutated_expr(index, out);
        }
        Expr::Binary { left, right, .. } => {
            collect_mutated_expr(left, out);
            collect_mutated_expr(right, out);
        }
        _ => {}
    }
}

// ============================================================================
// Swift 6 Lexer & Recursive-Descent Parser
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
enum SwiftTokKind {
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
    Arrow,
    DotDotLt,
    DotDotEq,
    Dot,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Bang,
    Eq,
    EqEq,
    BangEq,
    Lt,
    Le,
    Gt,
    Ge,
    AmpAmp,
    PipePipe,
    PlusEq,
    MinusEq,
}

#[derive(Debug, Clone)]
struct SwiftTok {
    kind: SwiftTokKind,
    line: usize,
    col: usize,
}

fn lex_swift(src: &str) -> Result<Vec<SwiftTok>, Diagnostic> {
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut line = 1;
    let mut col = 1;
    let mut tokens = Vec::new();

    while i < chars.len() {
        let ch = chars[i];
        if ch == '\n' {
            line += 1;
            col = 1;
            i += 1;
            continue;
        }
        if ch.is_whitespace() {
            col += 1;
            i += 1;
            continue;
        }
        // Line comment `// ...`
        if ch == '/' && i + 1 < chars.len() && chars[i + 1] == '/' {
            let s_col = col;
            i += 2;
            col += 2;
            let start = i;
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
                col += 1;
            }
            let text: String = chars[start..i].iter().collect();
            tokens.push(SwiftTok {
                kind: SwiftTokKind::Comment(text.trim().to_string()),
                line,
                col: s_col,
            });
            continue;
        }
        // Block comment `/* ... */`
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
        // String literal `"..."`
        if ch == '"' {
            let s_line = line;
            let s_col = col;
            i += 1;
            col += 1;
            let start = i;
            while i < chars.len() && chars[i] != '"' {
                if chars[i] == '\\' {
                    i += 1;
                    col += 1;
                }
                if i < chars.len() {
                    if chars[i] == '\n' {
                        line += 1;
                        col = 1;
                    } else {
                        col += 1;
                    }
                    i += 1;
                }
            }
            if i >= chars.len() {
                return Err(Diagnostic::new(
                    "swift",
                    "unterminated string literal",
                    s_line,
                    s_col,
                ));
            }
            let raw: String = chars[start..i].iter().collect();
            i += 1;
            col += 1;
            tokens.push(SwiftTok {
                kind: SwiftTokKind::Str(unescape_string(&raw)),
                line: s_line,
                col: s_col,
            });
            continue;
        }
        // Number literal
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
            let num_s: String = chars[start..i]
                .iter()
                .filter(|c| **c != '_')
                .collect();
            if is_float {
                let v = num_s.parse::<f64>().map_err(|_| {
                    Diagnostic::new(
                        "swift",
                        format!("invalid float literal '{}'", num_s),
                        line,
                        s_col,
                    )
                })?;
                tokens.push(SwiftTok {
                    kind: SwiftTokKind::Float(v),
                    line,
                    col: s_col,
                });
            } else {
                let v = num_s.parse::<i64>().map_err(|_| {
                    Diagnostic::new(
                        "swift",
                        format!("invalid integer literal '{}'", num_s),
                        line,
                        s_col,
                    )
                })?;
                tokens.push(SwiftTok {
                    kind: SwiftTokKind::Int(v),
                    line,
                    col: s_col,
                });
            }
            continue;
        }
        // Identifier / keyword
        if ch.is_ascii_alphabetic() || ch == '_' {
            let s_col = col;
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            let ident: String = chars[start..i].iter().collect();
            tokens.push(SwiftTok {
                kind: SwiftTokKind::Ident(ident),
                line,
                col: s_col,
            });
            continue;
        }

        let s_col = col;
        if i + 2 < chars.len() {
            let three = match (chars[i], chars[i + 1], chars[i + 2]) {
                ('.', '.', '<') => Some(SwiftTokKind::DotDotLt),
                ('.', '.', '.') => Some(SwiftTokKind::DotDotEq),
                _ => None,
            };
            if let Some(kind) = three {
                tokens.push(SwiftTok {
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
                ('-', '>') => Some(SwiftTokKind::Arrow),
                ('&', '&') => Some(SwiftTokKind::AmpAmp),
                ('|', '|') => Some(SwiftTokKind::PipePipe),
                ('=', '=') => Some(SwiftTokKind::EqEq),
                ('!', '=') => Some(SwiftTokKind::BangEq),
                ('<', '=') => Some(SwiftTokKind::Le),
                ('>', '=') => Some(SwiftTokKind::Ge),
                ('+', '=') => Some(SwiftTokKind::PlusEq),
                ('-', '=') => Some(SwiftTokKind::MinusEq),
                _ => None,
            };
            if let Some(kind) = two {
                tokens.push(SwiftTok {
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
            '(' => SwiftTokKind::LParen,
            ')' => SwiftTokKind::RParen,
            '{' => SwiftTokKind::LBrace,
            '}' => SwiftTokKind::RBrace,
            '[' => SwiftTokKind::LBracket,
            ']' => SwiftTokKind::RBracket,
            ',' => SwiftTokKind::Comma,
            ';' => SwiftTokKind::Semi,
            ':' => SwiftTokKind::Colon,
            '.' => SwiftTokKind::Dot,
            '+' => SwiftTokKind::Plus,
            '-' => SwiftTokKind::Minus,
            '*' => SwiftTokKind::Star,
            '/' => SwiftTokKind::Slash,
            '%' => SwiftTokKind::Percent,
            '!' => SwiftTokKind::Bang,
            '=' => SwiftTokKind::Eq,
            '<' => SwiftTokKind::Lt,
            '>' => SwiftTokKind::Gt,
            other => {
                return Err(Diagnostic::new(
                    "swift",
                    format!("unexpected character '{}'", other),
                    line,
                    s_col,
                ))
            }
        };
        tokens.push(SwiftTok {
            kind,
            line,
            col: s_col,
        });
        i += 1;
        col += 1;
    }

    Ok(tokens)
}

struct SwiftParser {
    tokens: Vec<SwiftTok>,
    pos: usize,
    known_structs: HashSet<String>,
    known_enums: HashSet<String>,
}

impl SwiftParser {
    fn cur_loc(&self) -> (usize, usize) {
        if let Some(tok) = self.tokens.get(self.pos) {
            (tok.line, tok.col)
        } else if let Some(last) = self.tokens.last() {
            (last.line, last.col + 1)
        } else {
            (1, 1)
        }
    }

    fn err<T>(&self, msg: impl Into<String>) -> Result<T, Diagnostic> {
        let (l, c) = self.cur_loc();
        Err(Diagnostic::new("swift", msg, l, c))
    }

    fn peek_kind(&self) -> Option<&SwiftTokKind> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn peek_kind_at(&self, offset: usize) -> Option<&SwiftTokKind> {
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<SwiftTok> {
        let tok = self.tokens.get(self.pos).cloned();
        if tok.is_some() {
            self.pos += 1;
        }
        tok
    }

    fn eat(&mut self, expected: &SwiftTokKind) -> bool {
        if self.peek_kind() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if matches!(self.peek_kind(), Some(SwiftTokKind::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &SwiftTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(expected) {
            Ok(())
        } else {
            self.err(format!("expected {}", label))
        }
    }

    fn expect_ident(&mut self) -> Result<String, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(SwiftTokKind::Ident(s)) => {
                self.pos += 1;
                Ok(s)
            }
            _ => self.err("expected identifier"),
        }
    }

    fn take_comments(&mut self) -> Vec<String> {
        let mut out = Vec::new();
        while let Some(SwiftTokKind::Comment(c)) = self.peek_kind().cloned() {
            self.pos += 1;
            out.push(c);
        }
        out
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut items = Vec::new();
        while self.pos < self.tokens.len() {
            let _ = self.eat(&SwiftTokKind::Semi);
            let comments = self.take_comments();
            if self.pos >= self.tokens.len() {
                break;
            }
            if self.eat_kw("import") {
                let _ = self.expect_ident()?;
                let _ = self.eat(&SwiftTokKind::Semi);
                continue;
            }
            // Optional visibility modifier (`public`, `internal`, `private`)
            let _ = self.eat_kw("public") || self.eat_kw("internal") || self.eat_kw("private");

            if self.eat_kw("struct") {
                items.push(Item::Struct(self.parse_struct(comments)?));
            } else if self.eat_kw("enum") {
                items.push(Item::Enum(self.parse_enum(comments)?));
            } else if self.eat_kw("func") {
                items.push(self.parse_fn_or_test(comments)?);
            } else if matches!(self.peek_kind(), Some(SwiftTokKind::Ident(s)) if s == "main")
                && matches!(self.peek_kind_at(1), Some(SwiftTokKind::LParen))
            {
                // Top-level `main()` entrypoint call
                self.pos += 2;
                self.expect(&SwiftTokKind::RParen, "')'")?;
                let _ = self.eat(&SwiftTokKind::Semi);
            } else {
                return self.err("expected 'struct', 'enum', or 'func' declaration in Swift");
            }
        }

        Ok(HubModule {
            next_id: 1,
            items,
        })
    }

    fn skip_protocol_conformances(&mut self) -> Result<(), Diagnostic> {
        if self.eat(&SwiftTokKind::Colon) {
            let _ = self.expect_ident()?;
            while self.eat(&SwiftTokKind::Comma) {
                let _ = self.expect_ident()?;
            }
        }
        Ok(())
    }

    fn parse_struct(&mut self, comments: Vec<String>) -> Result<StructDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.known_structs.insert(name.clone());
        self.skip_protocol_conformances()?;
        self.expect(&SwiftTokKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
            let _ = self.take_comments();
            if matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
                break;
            }
            let _ = self.eat_kw("public");
            if !(self.eat_kw("var") || self.eat_kw("let")) {
                return self.err("expected 'var' or 'let' field declaration in struct");
            }
            let fname = self.expect_ident()?;
            self.expect(&SwiftTokKind::Colon, "':'")?;
            let fty = self.parse_type()?;
            let _ = self.eat(&SwiftTokKind::Semi);
            fields.push(Field {
                id: 0,
                name: fname,
                ty: fty,
                meta: Metadata::new(),
            });
        }
        self.expect(&SwiftTokKind::RBrace, "'}'")?;
        Ok(StructDecl {
            id: 0,
            name,
            fields,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_enum(&mut self, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.known_enums.insert(name.clone());
        self.skip_protocol_conformances()?;
        self.expect(&SwiftTokKind::LBrace, "'{'")?;
        let mut variants = Vec::new();
        while !matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
            let _ = self.take_comments();
            if matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
                break;
            }
            if !self.eat_kw("case") {
                return self.err("expected 'case' in Swift enum");
            }
            variants.push(self.expect_ident()?);
            while self.eat(&SwiftTokKind::Comma) {
                variants.push(self.expect_ident()?);
            }
            let _ = self.eat(&SwiftTokKind::Semi);
        }
        self.expect(&SwiftTokKind::RBrace, "'}'")?;
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_fn_or_test(&mut self, comments: Vec<String>) -> Result<Item, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&SwiftTokKind::LParen, "'('")?;
        let mut params = Vec::new();
        while !matches!(self.peek_kind(), Some(SwiftTokKind::RParen) | None) {
            // Optional external argument label (`_` or external name) followed by internal parameter name
            let first = self.expect_ident()?;
            let pname = if matches!(self.peek_kind(), Some(SwiftTokKind::Ident(_))) {
                self.expect_ident()?
            } else {
                first
            };
            self.expect(&SwiftTokKind::Colon, "':'")?;
            let pty = self.parse_type()?;
            params.push(Param {
                id: 0,
                name: pname,
                ty: pty,
                meta: Metadata::new(),
            });
            if !self.eat(&SwiftTokKind::Comma) {
                break;
            }
        }
        self.expect(&SwiftTokKind::RParen, "')'")?;

        let ret_ty = if self.eat(&SwiftTokKind::Arrow) {
            if self.eat(&SwiftTokKind::LParen) {
                self.expect(&SwiftTokKind::RParen, "')'")?;
                Type::Void
            } else {
                self.parse_type()?
            }
        } else {
            Type::Void
        };

        let mut body = self.parse_block()?;

        // Strip Swift's parameter-mutability self-shadowing (`var p = p`) at function entry
        let param_names: HashSet<&str> = params.iter().map(|p| p.name.as_str()).collect();
        body.retain(|stmt| {
            if let Stmt::Let {
                name,
                mutable: true,
                ty: None,
                value: Expr::Var(rhs),
                ..
            } = stmt
            {
                if name == rhs && param_names.contains(name.as_str()) {
                    return false;
                }
            }
            true
        });

        if params.is_empty() && ret_ty == Type::Void {
            if let Some(stripped) = name.strip_prefix("test_") {
                if !stripped.is_empty() {
                    return Ok(Item::Test(TestDecl {
                        id: 0,
                        name: stripped.to_string(),
                        body,
                        comments,
                        meta: Metadata::new(),
                    }));
                }
            }
        }

        Ok(Item::Function(FnDecl {
            id: 0,
            name,
            params,
            ret_ty,
            body,
            comments,
            meta: Metadata::new(),
        }))
    }

    fn parse_type(&mut self) -> Result<Type, Diagnostic> {
        if self.eat(&SwiftTokKind::LBracket) {
            let inner = self.parse_type()?;
            self.expect(&SwiftTokKind::RBracket, "']'")?;
            return Ok(Type::List(Box::new(inner)));
        }
        let ident = self.expect_ident()?;
        if ident == "Array" && self.eat(&SwiftTokKind::Lt) {
            let inner = self.parse_type()?;
            self.expect(&SwiftTokKind::Gt, "'>'")?;
            return Ok(Type::List(Box::new(inner)));
        }
        match ident.as_str() {
            "Int" | "Int64" => Ok(Type::Int),
            "Double" | "Float" => Ok(Type::Float),
            "Bool" => Ok(Type::Bool),
            "String" => Ok(Type::Str),
            "Void" => Ok(Type::Void),
            other => Ok(Type::Named(other.to_string())),
        }
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        self.expect(&SwiftTokKind::LBrace, "'{'")?;
        let mut stmts = Vec::new();
        while !matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
            let _ = self.eat(&SwiftTokKind::Semi);
            if matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
                break;
            }
            if let Some(stmt) = self.parse_stmt()? {
                stmts.push(stmt);
            }
        }
        self.expect(&SwiftTokKind::RBrace, "'}'")?;
        Ok(stmts)
    }

    fn parse_stmt(&mut self) -> Result<Option<Stmt>, Diagnostic> {
        if let Some(SwiftTokKind::Comment(text)) = self.peek_kind().cloned() {
            self.pos += 1;
            return Ok(Some(Stmt::Comment { id: 0, text }));
        }
        // Ignore synthetic `fatalError(...)` reachability guards
        if matches!(self.peek_kind(), Some(SwiftTokKind::Ident(s)) if s == "fatalError")
            && matches!(self.peek_kind_at(1), Some(SwiftTokKind::LParen))
        {
            self.pos += 2;
            let _ = self.parse_call_args_unlabeled()?;
            let _ = self.eat(&SwiftTokKind::Semi);
            return Ok(None);
        }
        if self.eat_kw("let") {
            return self.parse_let(false).map(Some);
        }
        if self.eat_kw("var") {
            return self.parse_let(true).map(Some);
        }
        if self.eat_kw("if") {
            return self.parse_if().map(Some);
        }
        if self.eat_kw("switch") {
            return self.parse_switch().map(Some);
        }
        if self.eat_kw("while") {
            let cond = self.parse_expr()?;
            let body = self.parse_block()?;
            return Ok(Some(Stmt::While {
                id: 0,
                cond,
                body,
                meta: Metadata::new(),
            }));
        }
        if self.eat_kw("for") {
            return self.parse_for().map(Some);
        }
        if self.eat_kw("break") {
            let _ = self.eat(&SwiftTokKind::Semi);
            return Ok(Some(Stmt::Break { id: 0 }));
        }
        if self.eat_kw("continue") {
            let _ = self.eat(&SwiftTokKind::Semi);
            return Ok(Some(Stmt::Continue { id: 0 }));
        }
        if self.eat_kw("return") {
            if self.eat(&SwiftTokKind::Semi)
                || matches!(
                    self.peek_kind(),
                    Some(SwiftTokKind::RBrace) | None
                )
            {
                return Ok(Some(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                }));
            }
            // Note: in Swift without semicolons, check if the return keyword is on its own line
            // before another statement keyword (`case`, `default`, `}`).
            if matches!(
                self.peek_kind(),
                Some(SwiftTokKind::Ident(s)) if s == "case" || s == "default"
            ) {
                return Ok(Some(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                }));
            }
            let val = self.parse_expr()?;
            let _ = self.eat(&SwiftTokKind::Semi);
            return Ok(Some(Stmt::Return {
                id: 0,
                value: Some(val),
                meta: Metadata::new(),
            }));
        }
        if matches!(self.peek_kind(), Some(SwiftTokKind::Ident(s)) if s == "assert")
            && matches!(self.peek_kind_at(1), Some(SwiftTokKind::LParen))
        {
            self.pos += 2;
            let cond = self.parse_expr()?;
            // Optional failure message `, "msg"`
            if self.eat(&SwiftTokKind::Comma) {
                let _ = self.parse_expr()?;
            }
            self.expect(&SwiftTokKind::RParen, "')'")?;
            let _ = self.eat(&SwiftTokKind::Semi);
            if let Expr::Binary {
                op: BinOp::Eq,
                left,
                right,
            } = cond
            {
                return Ok(Some(Stmt::AssertEq {
                    id: 0,
                    left: *left,
                    right: *right,
                    meta: Metadata::new(),
                }));
            }
            return Ok(Some(Stmt::Assert {
                id: 0,
                cond,
                meta: Metadata::new(),
            }));
        }
        if matches!(self.peek_kind(), Some(SwiftTokKind::Ident(s)) if s == "assertEqual")
            && matches!(self.peek_kind_at(1), Some(SwiftTokKind::LParen))
        {
            self.pos += 2;
            let left = self.parse_expr()?;
            self.expect(&SwiftTokKind::Comma, "','")?;
            let right = self.parse_expr()?;
            self.expect(&SwiftTokKind::RParen, "')'")?;
            let _ = self.eat(&SwiftTokKind::Semi);
            return Ok(Some(Stmt::AssertEq {
                id: 0,
                left,
                right,
                meta: Metadata::new(),
            }));
        }

        let expr = self.parse_expr()?;
        if let Some(op) = match self.peek_kind() {
            Some(SwiftTokKind::Eq) => Some(AssignOp::Set),
            Some(SwiftTokKind::PlusEq) => Some(AssignOp::AddAssign),
            Some(SwiftTokKind::MinusEq) => Some(AssignOp::SubAssign),
            _ => None,
        } {
            self.pos += 1;
            let value = self.parse_expr()?;
            let _ = self.eat(&SwiftTokKind::Semi);
            let target = expr_to_assign_target(expr).ok_or_else(|| {
                let (l, c) = self.cur_loc();
                Diagnostic::new("swift", "invalid assignment target", l, c)
            })?;
            return Ok(Some(Stmt::Assign {
                id: 0,
                target,
                op,
                value,
                meta: Metadata::new(),
            }));
        }

        let _ = self.eat(&SwiftTokKind::Semi);
        Ok(Some(Stmt::Expr {
            id: 0,
            expr,
            meta: Metadata::new(),
        }))
    }

    fn parse_let(&mut self, mutable: bool) -> Result<Stmt, Diagnostic> {
        let name = self.expect_ident()?;
        let ty = if self.eat(&SwiftTokKind::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };
        self.expect(&SwiftTokKind::Eq, "'='")?;
        let value = self.parse_expr()?;
        let _ = self.eat(&SwiftTokKind::Semi);
        Ok(Stmt::Let {
            id: 0,
            name,
            mutable,
            ty,
            value,
            meta: Metadata::new(),
        })
    }

    fn parse_if(&mut self) -> Result<Stmt, Diagnostic> {
        let cond = self.parse_expr()?;
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
        let expr = self.parse_expr()?;
        self.expect(&SwiftTokKind::LBrace, "'{'")?;
        let mut arms = Vec::new();
        while !matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
            let _ = self.take_comments();
            if matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
                break;
            }
            let pat = if self.eat_kw("default") {
                MatchPat::Wildcard
            } else if self.eat_kw("case") {
                self.parse_match_pat()?
            } else {
                return self.err("expected 'case' or 'default' in Swift switch");
            };
            self.expect(&SwiftTokKind::Colon, "':'")?;

            let mut raw_body = Vec::new();
            let mut saw_fatal_error = false;
            while !matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
                if matches!(
                    self.peek_kind(),
                    Some(SwiftTokKind::Ident(s)) if s == "case" || s == "default"
                ) {
                    break;
                }
                let _ = self.eat(&SwiftTokKind::Semi);
                if matches!(self.peek_kind(), Some(SwiftTokKind::RBrace) | None) {
                    break;
                }
                if matches!(
                    self.peek_kind(),
                    Some(SwiftTokKind::Ident(s)) if s == "case" || s == "default"
                ) {
                    break;
                }
                if matches!(self.peek_kind(), Some(SwiftTokKind::Ident(s)) if s == "fatalError")
                    && matches!(self.peek_kind_at(1), Some(SwiftTokKind::LParen))
                {
                    saw_fatal_error = true;
                }
                if let Some(s) = self.parse_stmt()? {
                    raw_body.push(s);
                }
            }

            // Synthetic `default: fatalError("unreachable")` on Int/Str switches -> omit arm
            if pat == MatchPat::Wildcard && raw_body.is_empty() && saw_fatal_error {
                continue;
            }

            // If arm had only a required empty-arm `break` (plus optional comments), strip the `break`
            let exec_count = raw_body
                .iter()
                .filter(|s| !matches!(s, Stmt::Comment { .. }))
                .count();
            if exec_count == 1 && matches!(raw_body.last(), Some(Stmt::Break { .. })) {
                raw_body.pop();
            }

            arms.push(MatchArm { pat, body: raw_body });
        }
        self.expect(&SwiftTokKind::RBrace, "'}'")?;
        Ok(Stmt::Match {
            id: 0,
            expr,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_match_pat(&mut self) -> Result<MatchPat, Diagnostic> {
        if self.eat(&SwiftTokKind::Minus) {
            if let Some(SwiftTokKind::Int(v)) = self.peek_kind().cloned() {
                self.pos += 1;
                return Ok(MatchPat::Int(-v));
            }
            return self.err("expected integer literal after '-' in case pattern");
        }
        match self.peek_kind().cloned() {
            Some(SwiftTokKind::Int(v)) => {
                self.pos += 1;
                Ok(MatchPat::Int(v))
            }
            Some(SwiftTokKind::Str(s)) => {
                self.pos += 1;
                Ok(MatchPat::Str(s))
            }
            Some(SwiftTokKind::Ident(s)) if s == "_" => {
                self.pos += 1;
                Ok(MatchPat::Wildcard)
            }
            Some(SwiftTokKind::Ident(enum_name)) => {
                self.pos += 1;
                self.expect(&SwiftTokKind::Dot, "'.'")?;
                let variant = self.expect_ident()?;
                Ok(MatchPat::EnumVariant { enum_name, variant })
            }
            _ => self.err("unsupported Swift switch case pattern"),
        }
    }

    fn parse_for(&mut self) -> Result<Stmt, Diagnostic> {
        let _ = self.eat_kw("var");
        let var = self.expect_ident()?;
        self.expect(
            &SwiftTokKind::Ident("in".to_string()),
            "'in' in Swift for loop",
        )?;

        // Check `stride(from: start, to: end, by: 1)`
        if matches!(self.peek_kind(), Some(SwiftTokKind::Ident(s)) if s == "stride")
            && matches!(self.peek_kind_at(1), Some(SwiftTokKind::LParen))
        {
            self.pos += 2;
            let lbl1 = self.expect_ident()?;
            if lbl1 != "from" {
                return self.err("expected 'from:' in stride(...)");
            }
            self.expect(&SwiftTokKind::Colon, "':'")?;
            let start = self.parse_expr()?;
            self.expect(&SwiftTokKind::Comma, "','")?;
            let lbl2 = self.expect_ident()?;
            if lbl2 != "to" {
                return self.err("expected 'to:' in stride(...)");
            }
            self.expect(&SwiftTokKind::Colon, "':'")?;
            let end = self.parse_expr()?;
            self.expect(&SwiftTokKind::Comma, "','")?;
            let lbl3 = self.expect_ident()?;
            if lbl3 != "by" {
                return self.err("expected 'by:' in stride(...)");
            }
            self.expect(&SwiftTokKind::Colon, "':'")?;
            let _step = self.parse_expr()?;
            self.expect(&SwiftTokKind::RParen, "')'")?;
            let body = self.parse_block()?;
            return Ok(Stmt::ForRange {
                id: 0,
                var,
                start,
                end,
                body,
                meta: Metadata::new(),
            });
        }

        let first = self.parse_expr()?;
        if self.eat(&SwiftTokKind::DotDotLt) {
            let end = self.parse_expr()?;
            let body = self.parse_block()?;
            return Ok(Stmt::ForRange {
                id: 0,
                var,
                start: first,
                end,
                body,
                meta: Metadata::new(),
            });
        }
        if self.eat(&SwiftTokKind::DotDotEq) {
            let incl_end = self.parse_expr()?;
            let end = Expr::Binary {
                op: BinOp::Add,
                left: Box::new(incl_end),
                right: Box::new(Expr::Int(1)),
            };
            let body = self.parse_block()?;
            return Ok(Stmt::ForRange {
                id: 0,
                var,
                start: first,
                end,
                body,
                meta: Metadata::new(),
            });
        }

        let body = self.parse_block()?;
        Ok(Stmt::ForEach {
            id: 0,
            var,
            iter: first,
            body,
            meta: Metadata::new(),
        })
    }

    fn parse_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_and()?;
        while self.eat(&SwiftTokKind::PipePipe) {
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
        while self.eat(&SwiftTokKind::AmpAmp) {
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
        let mut left = self.parse_cast()?;
        loop {
            let op = match self.peek_kind() {
                Some(SwiftTokKind::EqEq) => Some(BinOp::Eq),
                Some(SwiftTokKind::BangEq) => Some(BinOp::Ne),
                Some(SwiftTokKind::Lt) => Some(BinOp::Lt),
                Some(SwiftTokKind::Le) => Some(BinOp::Le),
                Some(SwiftTokKind::Gt) => Some(BinOp::Gt),
                Some(SwiftTokKind::Ge) => Some(BinOp::Ge),
                _ => None,
            };
            if let Some(op) = op {
                self.pos += 1;
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
        let expr = self.parse_add()?;
        while self.eat_kw("as") {
            let _ = self.eat(&SwiftTokKind::Bang);
            let _ = self.parse_type()?;
        }
        Ok(expr)
    }

    fn parse_add(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_mul()?;
        loop {
            let op = match self.peek_kind() {
                Some(SwiftTokKind::Plus) => Some(BinOp::Add),
                Some(SwiftTokKind::Minus) => Some(BinOp::Sub),
                _ => None,
            };
            if let Some(op) = op {
                self.pos += 1;
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
                Some(SwiftTokKind::Star) => Some(BinOp::Mul),
                Some(SwiftTokKind::Slash) => Some(BinOp::Div),
                Some(SwiftTokKind::Percent) => Some(BinOp::Mod),
                _ => None,
            };
            if let Some(op) = op {
                self.pos += 1;
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
        if self.eat(&SwiftTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        if self.eat(&SwiftTokKind::Bang) {
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
            if self.eat(&SwiftTokKind::Dot) {
                let member = self.expect_ident()?;
                if self.eat(&SwiftTokKind::LParen) {
                    let mut args = self.parse_call_args_unlabeled()?;
                    base = match (member.as_str(), args.len()) {
                        ("append", 1) => Expr::intrinsic(Intrinsic::Push {
                            list: base,
                            value: args.pop().unwrap(),
                        }),
                        ("contains", 1) => Expr::intrinsic(Intrinsic::Contains {
                            haystack: base,
                            needle: args.pop().unwrap(),
                        }),
                        ("uppercased", 0) => Expr::intrinsic(Intrinsic::Upper(base)),
                        ("lowercased", 0) => Expr::intrinsic(Intrinsic::Lower(base)),
                        _ => {
                            return self.err(format!(
                                "unsupported Swift method '.{}(...)'",
                                member
                            ))
                        }
                    };
                } else if member == "count" {
                    base = Expr::intrinsic(Intrinsic::Len(base));
                } else if let Expr::Var(ref name) = base {
                    if self.known_enums.contains(name) {
                        base = Expr::EnumVariant {
                            enum_name: name.clone(),
                            variant: member,
                        };
                    } else {
                        base = Expr::FieldAccess {
                            base: Box::new(base),
                            field: member,
                        };
                    }
                } else {
                    base = Expr::FieldAccess {
                        base: Box::new(base),
                        field: member,
                    };
                }
            } else if self.eat(&SwiftTokKind::LBracket) {
                let idx = self.parse_expr()?;
                self.expect(&SwiftTokKind::RBracket, "']'")?;
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
            Some(SwiftTokKind::Int(v)) => {
                self.next();
                Ok(Expr::Int(v))
            }
            Some(SwiftTokKind::Float(v)) => {
                self.next();
                Ok(Expr::Float(v))
            }
            Some(SwiftTokKind::Str(s)) => {
                self.next();
                Ok(Expr::Str(s))
            }
            Some(SwiftTokKind::LParen) => {
                self.next();
                let e = self.parse_expr()?;
                self.expect(&SwiftTokKind::RParen, "')'")?;
                Ok(e)
            }
            Some(SwiftTokKind::LBracket) => {
                self.next();
                let mut items = Vec::new();
                while !matches!(self.peek_kind(), Some(SwiftTokKind::RBracket) | None) {
                    items.push(self.parse_expr()?);
                    if !self.eat(&SwiftTokKind::Comma) {
                        break;
                    }
                }
                self.expect(&SwiftTokKind::RBracket, "']'")?;
                Ok(Expr::List(items))
            }
            Some(SwiftTokKind::Ident(ident)) => {
                self.next();
                if ident == "true" {
                    return Ok(Expr::Bool(true));
                }
                if ident == "false" {
                    return Ok(Expr::Bool(false));
                }
                if self.eat(&SwiftTokKind::LParen) {
                    // Struct initializer if `ident` is a known struct OR arguments are `label: expr`
                    let is_labeled = matches!(self.peek_kind(), Some(SwiftTokKind::Ident(_)))
                        && matches!(self.peek_kind_at(1), Some(SwiftTokKind::Colon));
                    if self.known_structs.contains(&ident)
                        || (is_labeled
                            && ident != "String"
                            && ident != "Int"
                            && ident != "Double"
                            && ident != "print"
                            && ident != "min"
                            && ident != "max"
                            && ident != "abs")
                    {
                        let mut fields = Vec::new();
                        while !matches!(self.peek_kind(), Some(SwiftTokKind::RParen) | None) {
                            let fname = self.expect_ident()?;
                            self.expect(&SwiftTokKind::Colon, "':'")?;
                            let fval = self.parse_expr()?;
                            fields.push((fname, fval));
                            if !self.eat(&SwiftTokKind::Comma) {
                                break;
                            }
                        }
                        self.expect(&SwiftTokKind::RParen, "')'")?;
                        return Ok(Expr::StructInit {
                            name: ident,
                            fields,
                        });
                    }

                    let mut args = self.parse_call_args_unlabeled()?;
                    return match (ident.as_str(), args.len()) {
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
                        ("print", _) => Ok(Expr::intrinsic(Intrinsic::Print(args))),
                        ("String", 1) => {
                            Ok(Expr::intrinsic(Intrinsic::ToStr(args.pop().unwrap())))
                        }
                        ("Int" | "Int64" | "Double", 1) => Ok(args.pop().unwrap()),
                        _ => Ok(Expr::Call { func: ident, args }),
                    };
                }
                Ok(Expr::Var(ident))
            }
            _ => self.err("expected Swift expression"),
        }
    }

    fn parse_call_args_unlabeled(&mut self) -> Result<Vec<Expr>, Diagnostic> {
        let mut args = Vec::new();
        while !matches!(self.peek_kind(), Some(SwiftTokKind::RParen) | None) {
            // Allow optional `describing:` label in `String(describing: x)`
            if matches!(self.peek_kind(), Some(SwiftTokKind::Ident(s)) if s == "describing")
                && matches!(self.peek_kind_at(1), Some(SwiftTokKind::Colon))
            {
                self.pos += 2;
            }
            args.push(self.parse_expr()?);
            if !self.eat(&SwiftTokKind::Comma) {
                break;
            }
        }
        self.expect(&SwiftTokKind::RParen, "')'")?;
        Ok(args)
    }
}

fn expr_to_assign_target(expr: Expr) -> Option<AssignTarget> {
    match expr {
        Expr::Var(v) => Some(AssignTarget::Var(v)),
        Expr::FieldAccess { base, field } => {
            if let Expr::Var(b) = *base {
                Some(AssignTarget::Field { base: b, field })
            } else {
                None
            }
        }
        Expr::Index { base, index } => {
            if let Expr::Var(b) = *base {
                Some(AssignTarget::Index {
                    base: b,
                    index: *index,
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

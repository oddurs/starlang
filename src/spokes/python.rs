use std::collections::{HashMap, HashSet};

use crate::hub::{
    AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl, HubModule, Intrinsic,
    Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl, Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct PythonLens;

impl LanguageLens for PythonLens {
    fn id(&self) -> SpokeId {
        SpokeId::Python
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut out = String::new();
        let has_structs = hub.items.iter().any(|i| matches!(i, Item::Struct(_)));
        let has_enums = hub.items.iter().any(|i| matches!(i, Item::Enum(_)));
        if has_structs {
            out.push_str("from dataclasses import dataclass\n");
        }
        if has_enums {
            out.push_str("from enum import Enum\n");
        }
        if has_structs || has_enums {
            out.push('\n');
        }

        for (idx, item) in hub.items.iter().enumerate() {
            if idx > 0 {
                out.push_str("\n\n");
            }
            match item {
                Item::Struct(s) => fmt_struct(s, &mut out),
                Item::Enum(e) => fmt_enum(e, &mut out),
                Item::Function(f) => fmt_fn(f, &mut out),
                Item::Test(t) => fmt_test(t, &mut out),
            }
        }

        if hub.has_main() {
            if !out.is_empty() {
                out.push_str("\n\n");
            }
            out.push_str("if __name__ == \"__main__\":\n    main()\n");
        } else if !out.ends_with('\n') && !out.is_empty() {
            out.push('\n');
        }
        out
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_python(source)?;
        let mut known_structs: HashMap<String, Vec<String>> = HashMap::new();
        for item in &prev_hub.items {
            if let Item::Struct(s) = item {
                known_structs.insert(
                    s.name.clone(),
                    s.fields.iter().map(|f| f.name.clone()).collect(),
                );
            }
        }
        let mut parser = PyParser {
            tokens,
            pos: 0,
            known_structs,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Python))
    }
}

fn fmt_type(ty: &Type) -> String {
    match ty {
        Type::Int => "int".to_string(),
        Type::Float => "float".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Str => "str".to_string(),
        Type::Void => "None".to_string(),
        Type::List(inner) => format!("list[{}]", fmt_type(inner)),
        Type::Named(name) => name.clone(),
    }
}

fn fmt_struct(s: &StructDecl, out: &mut String) {
    for c in &s.comments {
        out.push_str(&format!("# {}\n", c));
    }
    out.push_str("@dataclass\n");
    out.push_str(&format!("class {}:\n", s.name));
    if s.fields.is_empty() {
        out.push_str("    pass\n");
    } else {
        for f in &s.fields {
            out.push_str(&format!("    {}: {}\n", f.name, fmt_type(&f.ty)));
        }
    }
    if out.ends_with('\n') {
        out.pop();
    }
}

fn fmt_enum(e: &EnumDecl, out: &mut String) {
    for c in &e.comments {
        out.push_str(&format!("# {}\n", c));
    }
    out.push_str(&format!("class {}(Enum):\n", e.name));
    if e.variants.is_empty() {
        out.push_str("    pass\n");
    } else {
        for (i, v) in e.variants.iter().enumerate() {
            out.push_str(&format!("    {} = {}\n", v, i));
        }
    }
    if out.ends_with('\n') {
        out.pop();
    }
}

fn fmt_fn(f: &FnDecl, out: &mut String) {
    for c in &f.comments {
        out.push_str(&format!("# {}\n", c));
    }
    let params_str: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, fmt_type(&p.ty)))
        .collect();
    out.push_str(&format!(
        "def {}({}) -> {}:\n",
        f.name,
        params_str.join(", "),
        fmt_type(&f.ret_ty)
    ));
    fmt_block(&f.body, 1, out);
    if out.ends_with('\n') {
        out.pop();
    }
}

fn fmt_test(t: &TestDecl, out: &mut String) {
    for c in &t.comments {
        out.push_str(&format!("# {}\n", c));
    }
    out.push_str(&format!("def test_{}() -> None:\n", t.name));
    fmt_block(&t.body, 1, out);
    if out.ends_with('\n') {
        out.pop();
    }
}

fn fmt_block(stmts: &[Stmt], indent: usize, out: &mut String) {
    let pad = "    ".repeat(indent);
    let has_executable = stmts.iter().any(|s| !matches!(s, Stmt::Comment { .. }));
    for stmt in stmts {
        fmt_stmt(stmt, indent, out);
    }
    if !has_executable {
        out.push_str(&format!("{}pass\n", pad));
    }
}

fn fmt_pat(pat: &MatchPat) -> String {
    match pat {
        MatchPat::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
        MatchPat::Int(v) => v.to_string(),
        MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
        MatchPat::Wildcard => "_".to_string(),
    }
}

fn fmt_stmt(stmt: &Stmt, indent: usize, out: &mut String) {
    let pad = "    ".repeat(indent);
    match stmt {
        Stmt::Comment { text, .. } => {
            out.push_str(&format!("{}# {}\n", pad, text));
        }
        Stmt::Let {
            name, ty, value, ..
        } => {
            if let Some(t) = ty {
                out.push_str(&format!(
                    "{}{}: {} = {}\n",
                    pad,
                    name,
                    fmt_type(t),
                    fmt_expr(value)
                ));
            } else {
                out.push_str(&format!("{}{} = {}\n", pad, name, fmt_expr(value)));
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
                    format!("{}[{}]", base, fmt_expr(index))
                }
            };
            out.push_str(&format!("{}{} {} {}\n", pad, tgt, op_str, fmt_expr(value)));
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            fmt_if_chain(cond, then_body, else_body, indent, true, out);
        }
        Stmt::Match { expr, arms, .. } => {
            out.push_str(&format!("{}match {}:\n", pad, fmt_expr(expr)));
            for arm in arms {
                out.push_str(&format!("{}    case {}:\n", pad, fmt_pat(&arm.pat)));
                fmt_block(&arm.body, indent + 2, out);
            }
        }
        Stmt::While { cond, body, .. } => {
            out.push_str(&format!("{}while {}:\n", pad, fmt_expr(cond)));
            fmt_block(body, indent + 1, out);
        }
        Stmt::ForEach {
            var, iter, body, ..
        } => {
            out.push_str(&format!("{}for {} in {}:\n", pad, var, fmt_expr(iter)));
            fmt_block(body, indent + 1, out);
        }
        Stmt::ForRange {
            var,
            start,
            end,
            body,
            ..
        } => {
            out.push_str(&format!(
                "{}for {} in range({}, {}):\n",
                pad,
                var,
                fmt_expr(start),
                fmt_expr(end)
            ));
            fmt_block(body, indent + 1, out);
        }
        Stmt::Break { .. } => out.push_str(&format!("{}break\n", pad)),
        Stmt::Continue { .. } => out.push_str(&format!("{}continue\n", pad)),
        Stmt::Return { value, .. } => match value {
            Some(v) => out.push_str(&format!("{}return {}\n", pad, fmt_expr(v))),
            None => out.push_str(&format!("{}return\n", pad)),
        },
        Stmt::Assert { cond, .. } => {
            out.push_str(&format!("{}assert {}\n", pad, fmt_expr(cond)));
        }
        Stmt::AssertEq { left, right, .. } => {
            let eq_expr = Expr::Binary {
                op: BinOp::Eq,
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            };
            out.push_str(&format!("{}assert {}\n", pad, fmt_expr(&eq_expr)));
        }
        Stmt::Expr { expr, .. } => {
            out.push_str(&format!("{}{}\n", pad, fmt_expr(expr)));
        }
    }
}

fn fmt_if_chain(
    cond: &Expr,
    then_body: &[Stmt],
    else_body: &[Stmt],
    indent: usize,
    first: bool,
    out: &mut String,
) {
    let pad = "    ".repeat(indent);
    if first {
        out.push_str(&format!("{}if {}:\n", pad, fmt_expr(cond)));
    } else {
        out.push_str(&format!("{}elif {}:\n", pad, fmt_expr(cond)));
    }
    fmt_block(then_body, indent + 1, out);

    if else_body.len() == 1 && matches!(&else_body[0], Stmt::If { .. }) {
        if let Stmt::If {
            cond: c2,
            then_body: t2,
            else_body: e2,
            ..
        } = &else_body[0]
        {
            fmt_if_chain(c2, t2, e2, indent, false, out);
        }
    } else if !else_body.is_empty() {
        out.push_str(&format!("{}else:\n", pad));
        fmt_block(else_body, indent + 1, out);
    }
}

fn fmt_postfix(expr: &Expr) -> String {
    let s = fmt_expr(expr);
    match expr {
        Expr::Binary { .. } | Expr::Unary { .. } => format!("({})", s),
        Expr::Intrinsic(intr) if matches!(intr.as_ref(), Intrinsic::Contains { .. }) => {
            format!("({})", s)
        }
        _ => s,
    }
}

fn fmt_expr(expr: &Expr) -> String {
    match expr {
        Expr::Int(v) => v.to_string(),
        Expr::Float(v) => format_float(*v),
        Expr::Bool(b) => if *b { "True" } else { "False" }.to_string(),
        Expr::Str(s) => format!("\"{}\"", escape_str(s)),
        Expr::Var(v) => v.clone(),
        Expr::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
        Expr::List(items) => {
            let inner: Vec<String> = items.iter().map(fmt_expr).collect();
            format!("[{}]", inner.join(", "))
        }
        Expr::StructInit { name, fields } => {
            let inner: Vec<String> = fields
                .iter()
                .map(|(fname, fval)| format!("{}={}", fname, fmt_expr(fval)))
                .collect();
            format!("{}({})", name, inner.join(", "))
        }
        Expr::FieldAccess { base, field } => format!("{}.{}", fmt_postfix(base), field),
        Expr::Index { base, index } => format!("{}[{}]", fmt_postfix(base), fmt_expr(index)),
        Expr::Unary { op, expr: inner } => match op {
            UnaryOp::Neg => match inner.as_ref() {
                Expr::Binary { .. } | Expr::Unary { .. } => format!("-({})", fmt_expr(inner)),
                _ => format!("-{}", fmt_expr(inner)),
            },
            UnaryOp::Not => {
                if let Expr::Intrinsic(intr) = inner.as_ref() {
                    if let Intrinsic::Contains { haystack, needle } = intr.as_ref() {
                        return format!(
                            "{} not in {}",
                            fmt_postfix(needle),
                            fmt_postfix(haystack)
                        );
                    }
                }
                match inner.as_ref() {
                    Expr::Binary {
                        op: BinOp::And | BinOp::Or,
                        ..
                    } => format!("not ({})", fmt_expr(inner)),
                    _ => format!("not {}", fmt_expr(inner)),
                }
            }
        },
        Expr::Binary { op, left, right } => {
            let wrap_contains = |e: &Expr| -> Option<String> {
                if let Expr::Intrinsic(intr) = e {
                    if matches!(intr.as_ref(), Intrinsic::Contains { .. })
                        && !matches!(op, BinOp::And | BinOp::Or)
                    {
                        return Some(format!("({})", fmt_expr(e)));
                    }
                }
                None
            };
            let l_str = wrap_contains(left).unwrap_or_else(|| {
                if needs_parens(left, *op, false) {
                    format!("({})", fmt_expr(left))
                } else {
                    fmt_expr(left)
                }
            });
            let r_str = wrap_contains(right).unwrap_or_else(|| {
                if needs_parens(right, *op, true) {
                    format!("({})", fmt_expr(right))
                } else {
                    fmt_expr(right)
                }
            });
            let op_str = match op {
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
                BinOp::And => "and",
                BinOp::Or => "or",
            };
            format!("{} {} {}", l_str, op_str, r_str)
        }
        Expr::Call { func, args } => {
            let inner: Vec<String> = args.iter().map(fmt_expr).collect();
            format!("{}({})", func, inner.join(", "))
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(e) => format!("len({})", fmt_expr(e)),
            Intrinsic::Min(a, b) => format!("min({}, {})", fmt_expr(a), fmt_expr(b)),
            Intrinsic::Max(a, b) => format!("max({}, {})", fmt_expr(a), fmt_expr(b)),
            Intrinsic::Abs(a) => format!("abs({})", fmt_expr(a)),
            Intrinsic::Push { list, value } => {
                format!("{}.append({})", fmt_postfix(list), fmt_expr(value))
            }
            Intrinsic::Print(args) => {
                let inner: Vec<String> = args.iter().map(fmt_expr).collect();
                format!("print({})", inner.join(", "))
            }
            Intrinsic::Contains { haystack, needle } => {
                format!("{} in {}", fmt_postfix(needle), fmt_postfix(haystack))
            }
            Intrinsic::Upper(e) => format!("{}.upper()", fmt_postfix(e)),
            Intrinsic::Lower(e) => format!("{}.lower()", fmt_postfix(e)),
            Intrinsic::ToStr(e) => format!("str({})", fmt_expr(e)),
        },
    }
}

#[derive(Debug, Clone, PartialEq)]
enum PTokKind {
    Ident(String),
    Int(i64),
    Float(f64),
    Str(String),
    Comment(String),
    Newline,
    Indent,
    Dedent,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Colon,
    Dot,
    Arrow,
    At,
    Plus,
    Minus,
    Star,
    Slash,
    SlashSlash,
    Percent,
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
struct PTok {
    kind: PTokKind,
    line: usize,
    col: usize,
}

fn lex_python(src: &str) -> Result<Vec<PTok>, Diagnostic> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut line = 1;
    let mut indent_stack: Vec<usize> = vec![0];
    let mut bracket_depth: usize = 0;
    let mut at_line_start = true;

    while i < chars.len() {
        if at_line_start && bracket_depth == 0 {
            let mut spaces = 0usize;
            while i < chars.len() {
                if chars[i] == ' ' {
                    spaces += 1;
                    i += 1;
                } else if chars[i] == '\t' {
                    spaces += 4;
                    i += 1;
                } else {
                    break;
                }
            }
            if i >= chars.len() {
                break;
            }
            if chars[i] == '\r' {
                i += 1;
                if i < chars.len() && chars[i] == '\n' {
                    i += 1;
                }
                line += 1;
                continue;
            }
            if chars[i] == '\n' {
                i += 1;
                line += 1;
                continue;
            }

            let cur_indent = *indent_stack.last().unwrap();
            if spaces > cur_indent {
                indent_stack.push(spaces);
                tokens.push(PTok {
                    kind: PTokKind::Indent,
                    line,
                    col: 1,
                });
            } else if spaces < cur_indent {
                while let Some(&top) = indent_stack.last() {
                    if top > spaces {
                        indent_stack.pop();
                        tokens.push(PTok {
                            kind: PTokKind::Dedent,
                            line,
                            col: 1,
                        });
                    } else {
                        break;
                    }
                }
                if *indent_stack.last().unwrap() != spaces {
                    return Err(Diagnostic::new(
                        "python",
                        "inconsistent indentation level",
                        line,
                        spaces + 1,
                    ));
                }
            }
            at_line_start = false;
        }

        let ch = chars[i];
        let col = 1;

        if ch == '\r' {
            i += 1;
            continue;
        }
        if ch == '\n' {
            i += 1;
            if bracket_depth == 0 {
                if !matches!(
                    tokens.last().map(|t| &t.kind),
                    None | Some(PTokKind::Newline)
                        | Some(PTokKind::Indent)
                        | Some(PTokKind::Dedent)
                ) {
                    tokens.push(PTok {
                        kind: PTokKind::Newline,
                        line,
                        col,
                    });
                }
                at_line_start = true;
            }
            line += 1;
            continue;
        }
        if ch == ' ' || ch == '\t' {
            i += 1;
            continue;
        }
        if ch == '#' {
            i += 1;
            if i < chars.len() && chars[i] == ' ' {
                i += 1;
            }
            let start = i;
            while i < chars.len() && chars[i] != '\n' && chars[i] != '\r' {
                i += 1;
            }
            let text: String = chars[start..i].iter().collect();
            tokens.push(PTok {
                kind: PTokKind::Comment(text),
                line,
                col,
            });
            continue;
        }
        if ch == '"' || ch == '\'' {
            let quote = ch;
            let s_line = line;
            i += 1;
            let mut raw = String::new();
            let mut closed = false;
            while i < chars.len() {
                let c = chars[i];
                if c == quote {
                    i += 1;
                    closed = true;
                    break;
                }
                if c == '\\' && i + 1 < chars.len() {
                    raw.push('\\');
                    raw.push(chars[i + 1]);
                    i += 2;
                    continue;
                }
                if c == '\n' {
                    line += 1;
                }
                raw.push(c);
                i += 1;
            }
            if !closed {
                return Err(Diagnostic::new(
                    "python",
                    "unterminated string literal",
                    s_line,
                    col,
                ));
            }
            tokens.push(PTok {
                kind: PTokKind::Str(unescape_string(&raw)),
                line: s_line,
                col,
            });
            continue;
        }
        if ch.is_ascii_digit() {
            let start = i;
            let mut is_float = false;
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                i += 1;
            }
            if i + 1 < chars.len() && chars[i] == '.' && chars[i + 1].is_ascii_digit() {
                is_float = true;
                i += 1;
                while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                    i += 1;
                }
            }
            let num_str: String = chars[start..i].iter().filter(|c| **c != '_').collect();
            if is_float {
                let v = num_str.parse::<f64>().map_err(|_| {
                    Diagnostic::new("python", "invalid float literal", line, col)
                })?;
                tokens.push(PTok {
                    kind: PTokKind::Float(v),
                    line,
                    col,
                });
            } else {
                let v = num_str.parse::<i64>().map_err(|_| {
                    Diagnostic::new("python", "invalid integer literal", line, col)
                })?;
                tokens.push(PTok {
                    kind: PTokKind::Int(v),
                    line,
                    col,
                });
            }
            continue;
        }
        if ch.is_ascii_alphabetic() || ch == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let ident: String = chars[start..i].iter().collect();
            tokens.push(PTok {
                kind: PTokKind::Ident(ident),
                line,
                col,
            });
            continue;
        }

        if i + 1 < chars.len() {
            let two = match (chars[i], chars[i + 1]) {
                ('-', '>') => Some(PTokKind::Arrow),
                ('/', '/') => Some(PTokKind::SlashSlash),
                ('=', '=') => Some(PTokKind::EqEq),
                ('!', '=') => Some(PTokKind::BangEq),
                ('<', '=') => Some(PTokKind::Le),
                ('>', '=') => Some(PTokKind::Ge),
                ('+', '=') => Some(PTokKind::PlusEq),
                ('-', '=') => Some(PTokKind::MinusEq),
                _ => None,
            };
            if let Some(kind) = two {
                tokens.push(PTok { kind, line, col });
                i += 2;
                continue;
            }
        }

        let kind = match ch {
            '(' => {
                bracket_depth += 1;
                PTokKind::LParen
            }
            ')' => {
                bracket_depth = bracket_depth.saturating_sub(1);
                PTokKind::RParen
            }
            '[' => {
                bracket_depth += 1;
                PTokKind::LBracket
            }
            ']' => {
                bracket_depth = bracket_depth.saturating_sub(1);
                PTokKind::RBracket
            }
            ',' => PTokKind::Comma,
            ':' => PTokKind::Colon,
            '.' => PTokKind::Dot,
            '@' => PTokKind::At,
            '+' => PTokKind::Plus,
            '-' => PTokKind::Minus,
            '*' => PTokKind::Star,
            '/' => PTokKind::Slash,
            '%' => PTokKind::Percent,
            '=' => PTokKind::Eq,
            '<' => PTokKind::Lt,
            '>' => PTokKind::Gt,
            other => {
                return Err(Diagnostic::new(
                    "python",
                    format!("unexpected character '{}'", other),
                    line,
                    col,
                ))
            }
        };
        tokens.push(PTok { kind, line, col });
        i += 1;
    }

    if bracket_depth > 0 {
        return Err(Diagnostic::new("python", "unclosed '(' or '['", line, 1));
    }

    if !matches!(
        tokens.last().map(|t| &t.kind),
        None | Some(PTokKind::Newline) | Some(PTokKind::Dedent)
    ) {
        tokens.push(PTok {
            kind: PTokKind::Newline,
            line,
            col: 1,
        });
    }

    while indent_stack.len() > 1 {
        indent_stack.pop();
        tokens.push(PTok {
            kind: PTokKind::Dedent,
            line,
            col: 1,
        });
    }

    Ok(tokens)
}

struct PyParser {
    tokens: Vec<PTok>,
    pos: usize,
    known_structs: HashMap<String, Vec<String>>,
}

impl PyParser {
    fn peek(&self) -> Option<&PTok> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&PTokKind> {
        self.peek().map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<PTok> {
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
        Err(Diagnostic::new("python", msg, line, col))
    }

    fn eat(&mut self, expected: &PTokKind) -> bool {
        if self.peek_kind() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if matches!(self.peek_kind(), Some(PTokKind::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &PTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(expected) {
            Ok(())
        } else {
            self.err(format!("expected {}", label))
        }
    }

    fn expect_ident(&mut self) -> Result<String, Diagnostic> {
        match self.next() {
            Some(PTok {
                kind: PTokKind::Ident(s),
                ..
            }) => Ok(s),
            _ => self.err("expected identifier"),
        }
    }

    fn skip_newlines(&mut self) {
        while self.eat(&PTokKind::Newline) {}
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut module = HubModule::new();
        let mut comments = Vec::new();

        while self.peek().is_some() {
            self.skip_newlines();
            if self.peek().is_none() {
                break;
            }
            if let Some(PTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.next();
                self.skip_newlines();
                comments.push(c);
                continue;
            }
            if self.eat_kw("from") || self.eat_kw("import") {
                while !matches!(self.peek_kind(), Some(PTokKind::Newline) | None) {
                    self.next();
                }
                self.skip_newlines();
                continue;
            }
            if self.eat(&PTokKind::At) {
                while !matches!(self.peek_kind(), Some(PTokKind::Newline) | None) {
                    self.next();
                }
                self.skip_newlines();
                continue;
            }
            if matches!(self.peek_kind(), Some(PTokKind::Ident(s)) if s == "if") {
                let saved = self.pos;
                self.next();
                if matches!(self.peek_kind(), Some(PTokKind::Ident(s)) if s == "__name__") {
                    self.skip_indented_suite()?;
                    continue;
                }
                self.pos = saved;
            }

            let item_comments = std::mem::take(&mut comments);
            if self.eat_kw("class") {
                let name = self.expect_ident()?;
                if self.eat(&PTokKind::LParen) {
                    let base = self.expect_ident()?;
                    self.expect(&PTokKind::RParen, "')'")?;
                    if base == "Enum" || base == "IntEnum" {
                        let e = self.parse_enum(name, item_comments)?;
                        module.items.push(Item::Enum(e));
                        continue;
                    }
                }
                let s = self.parse_struct(name, item_comments)?;
                self.known_structs.insert(
                    s.name.clone(),
                    s.fields.iter().map(|f| f.name.clone()).collect(),
                );
                module.items.push(Item::Struct(s));
            } else if self.eat_kw("def") {
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
                return self.err("expected 'class' or 'def' at top level");
            }
        }

        Ok(module)
    }

    fn skip_indented_suite(&mut self) -> Result<(), Diagnostic> {
        while !matches!(self.peek_kind(), Some(PTokKind::Indent) | None) {
            self.next();
        }
        if self.eat(&PTokKind::Indent) {
            let mut depth = 1;
            while depth > 0 && self.peek().is_some() {
                match self.next().map(|t| t.kind) {
                    Some(PTokKind::Indent) => depth += 1,
                    Some(PTokKind::Dedent) => depth -= 1,
                    _ => {}
                }
            }
        }
        Ok(())
    }

    fn parse_struct(
        &mut self,
        name: String,
        comments: Vec<String>,
    ) -> Result<StructDecl, Diagnostic> {
        self.expect(&PTokKind::Colon, "':' after class name")?;
        self.skip_newlines();
        self.expect(&PTokKind::Indent, "indented class body")?;

        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), Some(PTokKind::Dedent) | None) {
            self.skip_newlines();
            if matches!(self.peek_kind(), Some(PTokKind::Dedent) | None) {
                break;
            }
            if let Some(PTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            if self.eat_kw("pass") {
                self.skip_newlines();
                continue;
            }
            let fname = self.expect_ident()?;
            self.expect(&PTokKind::Colon, "':' after field name")?;
            let fty = self.parse_type()?;
            self.skip_newlines();
            fields.push(Field {
                id: 0,
                name: fname,
                ty: fty,
                meta: Metadata::new(),
            });
        }
        self.expect(&PTokKind::Dedent, "end of class body")?;
        Ok(StructDecl {
            id: 0,
            name,
            fields,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_enum(&mut self, name: String, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        self.expect(&PTokKind::Colon, "':' after Enum class")?;
        self.skip_newlines();
        self.expect(&PTokKind::Indent, "indented Enum body")?;

        let mut variants = Vec::new();
        while !matches!(self.peek_kind(), Some(PTokKind::Dedent) | None) {
            self.skip_newlines();
            if matches!(self.peek_kind(), Some(PTokKind::Dedent) | None) {
                break;
            }
            if let Some(PTokKind::Comment(_)) = self.peek_kind() {
                self.next();
                continue;
            }
            if self.eat_kw("pass") {
                self.skip_newlines();
                continue;
            }
            let vname = self.expect_ident()?;
            if self.eat(&PTokKind::Eq) {
                let _ = self.parse_expr()?;
            }
            self.skip_newlines();
            variants.push(vname);
        }
        self.expect(&PTokKind::Dedent, "end of Enum body")?;
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_fn(&mut self, comments: Vec<String>) -> Result<FnDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&PTokKind::LParen, "'('")?;
        let mut params = Vec::new();
        let mut scope = HashSet::new();
        while !matches!(self.peek_kind(), Some(PTokKind::RParen) | None) {
            let pname = self.expect_ident()?;
            let pty = if self.eat(&PTokKind::Colon) {
                self.parse_type()?
            } else {
                Type::Int
            };
            scope.insert(pname.clone());
            params.push(Param {
                id: 0,
                name: pname,
                ty: pty,
                meta: Metadata::new(),
            });
            if !self.eat(&PTokKind::Comma) {
                break;
            }
        }
        self.expect(&PTokKind::RParen, "')'")?;

        let ret_ty = if self.eat(&PTokKind::Arrow) {
            self.parse_type()?
        } else {
            Type::Void
        };
        self.expect(&PTokKind::Colon, "':' after function signature")?;
        let body = self.parse_suite(&mut scope)?;

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
        match ident.as_str() {
            "int" => Ok(Type::Int),
            "float" => Ok(Type::Float),
            "bool" => Ok(Type::Bool),
            "str" => Ok(Type::Str),
            "None" => Ok(Type::Void),
            "list" | "List" | "Sequence" => {
                if self.eat(&PTokKind::LBracket) {
                    let inner = self.parse_type()?;
                    self.expect(&PTokKind::RBracket, "']'")?;
                    Ok(Type::list(inner))
                } else {
                    Ok(Type::list(Type::Int))
                }
            }
            other => Ok(Type::Named(other.to_string())),
        }
    }

    fn parse_suite(
        &mut self,
        enclosing_scope: &mut HashSet<String>,
    ) -> Result<Vec<Stmt>, Diagnostic> {
        self.skip_newlines();
        self.expect(&PTokKind::Indent, "indented block")?;
        let mut stmts = Vec::new();
        let mut local_scope = enclosing_scope.clone();

        while !matches!(self.peek_kind(), Some(PTokKind::Dedent) | None) {
            self.skip_newlines();
            if matches!(self.peek_kind(), Some(PTokKind::Dedent) | None) {
                break;
            }
            if let Some(PTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.next();
                self.skip_newlines();
                stmts.push(Stmt::Comment { id: 0, text: c });
                continue;
            }
            if self.eat_kw("pass") {
                self.skip_newlines();
                continue;
            }
            if self.eat_kw("if") {
                stmts.push(self.parse_if(&mut local_scope)?);
                continue;
            }
            if self.eat_kw("match") {
                stmts.push(self.parse_match(&mut local_scope)?);
                continue;
            }
            if self.eat_kw("while") {
                let cond = self.parse_expr()?;
                self.expect(&PTokKind::Colon, "':' after while condition")?;
                let body = self.parse_suite(&mut local_scope)?;
                stmts.push(Stmt::While {
                    id: 0,
                    cond,
                    body,
                    meta: Metadata::new(),
                });
                continue;
            }
            if self.eat_kw("for") {
                let var = self.expect_ident()?;
                if !self.eat_kw("in") {
                    return self.err("expected 'in' inside 'for' loop");
                }
                let iter_expr = self.parse_expr()?;
                self.expect(&PTokKind::Colon, "':' after for header")?;
                let mut loop_scope = local_scope.clone();
                loop_scope.insert(var.clone());
                let body = self.parse_suite(&mut loop_scope)?;

                match iter_expr {
                    Expr::Call { func, mut args } if func == "range" && args.len() == 1 => {
                        let end = args.pop().unwrap();
                        stmts.push(Stmt::ForRange {
                            id: 0,
                            var,
                            start: Expr::Int(0),
                            end,
                            body,
                            meta: Metadata::new(),
                        });
                    }
                    Expr::Call { func, mut args } if func == "range" && args.len() == 2 => {
                        let end = args.pop().unwrap();
                        let start = args.pop().unwrap();
                        stmts.push(Stmt::ForRange {
                            id: 0,
                            var,
                            start,
                            end,
                            body,
                            meta: Metadata::new(),
                        });
                    }
                    other => {
                        stmts.push(Stmt::ForEach {
                            id: 0,
                            var,
                            iter: other,
                            body,
                            meta: Metadata::new(),
                        });
                    }
                }
                continue;
            }
            if self.eat_kw("break") {
                self.skip_newlines();
                stmts.push(Stmt::Break { id: 0 });
                continue;
            }
            if self.eat_kw("continue") {
                self.skip_newlines();
                stmts.push(Stmt::Continue { id: 0 });
                continue;
            }
            if self.eat_kw("return") {
                if matches!(
                    self.peek_kind(),
                    Some(PTokKind::Newline) | Some(PTokKind::Dedent) | None
                ) {
                    self.skip_newlines();
                    stmts.push(Stmt::Return {
                        id: 0,
                        value: None,
                        meta: Metadata::new(),
                    });
                } else {
                    let val = self.parse_expr()?;
                    self.skip_newlines();
                    stmts.push(Stmt::Return {
                        id: 0,
                        value: Some(val),
                        meta: Metadata::new(),
                    });
                }
                continue;
            }
            if self.eat_kw("assert") {
                let cond = self.parse_expr()?;
                if self.eat(&PTokKind::Comma) {
                    let _ = self.parse_expr()?;
                }
                self.skip_newlines();
                stmts.push(Stmt::Assert {
                    id: 0,
                    cond,
                    meta: Metadata::new(),
                });
                continue;
            }

            if let Some(PTokKind::Ident(var_name)) = self.peek_kind().cloned() {
                if matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(PTokKind::Colon)
                ) {
                    self.next();
                    self.next();
                    let ty = self.parse_type()?;
                    self.expect(&PTokKind::Eq, "'=' after type annotation")?;
                    let value = self.parse_expr()?;
                    self.skip_newlines();
                    local_scope.insert(var_name.clone());
                    stmts.push(Stmt::Let {
                        id: 0,
                        name: var_name,
                        mutable: false,
                        ty: Some(ty),
                        value,
                        meta: Metadata::new(),
                    });
                    continue;
                }
            }

            let expr = self.parse_expr()?;
            if let Some(op) = match self.peek_kind() {
                Some(PTokKind::Eq) => Some(AssignOp::Set),
                Some(PTokKind::PlusEq) => Some(AssignOp::AddAssign),
                Some(PTokKind::MinusEq) => Some(AssignOp::SubAssign),
                _ => None,
            } {
                self.next();
                let value = self.parse_expr()?;
                self.skip_newlines();
                if let Expr::Var(v) = &expr {
                    if op == AssignOp::Set && !local_scope.contains(v) {
                        let name = v.clone();
                        local_scope.insert(name.clone());
                        stmts.push(Stmt::Let {
                            id: 0,
                            name,
                            mutable: false,
                            ty: None,
                            value,
                            meta: Metadata::new(),
                        });
                        continue;
                    }
                }
                let target = py_expr_to_target(expr)?;
                stmts.push(Stmt::Assign {
                    id: 0,
                    target,
                    op,
                    value,
                    meta: Metadata::new(),
                });
            } else {
                self.skip_newlines();
                stmts.push(Stmt::Expr {
                    id: 0,
                    expr,
                    meta: Metadata::new(),
                });
            }
        }

        self.expect(&PTokKind::Dedent, "end of indented block")?;
        Ok(stmts)
    }

    fn parse_if(&mut self, scope: &mut HashSet<String>) -> Result<Stmt, Diagnostic> {
        let cond = self.parse_expr()?;
        self.expect(&PTokKind::Colon, "':' after if/elif condition")?;
        let then_body = self.parse_suite(scope)?;
        self.skip_newlines();
        let else_body = if self.eat_kw("elif") {
            vec![self.parse_if(scope)?]
        } else if self.eat_kw("else") {
            self.expect(&PTokKind::Colon, "':' after else")?;
            self.parse_suite(scope)?
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

    fn parse_match(&mut self, scope: &mut HashSet<String>) -> Result<Stmt, Diagnostic> {
        let expr = self.parse_expr()?;
        self.expect(&PTokKind::Colon, "':' after match")?;
        self.skip_newlines();
        self.expect(&PTokKind::Indent, "indented match cases")?;
        let mut arms = Vec::new();
        while !matches!(self.peek_kind(), Some(PTokKind::Dedent) | None) {
            self.skip_newlines();
            if matches!(self.peek_kind(), Some(PTokKind::Dedent) | None) {
                break;
            }
            if !self.eat_kw("case") {
                return self.err("expected 'case' inside match");
            }
            let pat = match self.peek_kind().cloned() {
                Some(PTokKind::Ident(s)) if s == "_" => {
                    self.next();
                    MatchPat::Wildcard
                }
                Some(PTokKind::Int(v)) => {
                    self.next();
                    MatchPat::Int(v)
                }
                Some(PTokKind::Minus) => {
                    self.next();
                    if let Some(PTokKind::Int(v)) = self.peek_kind().cloned() {
                        self.next();
                        MatchPat::Int(-v)
                    } else {
                        return self.err("expected integer in negative case pattern");
                    }
                }
                Some(PTokKind::Str(s)) => {
                    self.next();
                    MatchPat::Str(s)
                }
                Some(PTokKind::Ident(ename)) => {
                    self.next();
                    self.expect(&PTokKind::Dot, "'.' in Enum.Variant case pattern")?;
                    let variant = self.expect_ident()?;
                    MatchPat::EnumVariant {
                        enum_name: ename,
                        variant,
                    }
                }
                _ => return self.err("invalid Python match case pattern"),
            };
            self.expect(&PTokKind::Colon, "':' after case pattern")?;
            let body = self.parse_suite(scope)?;
            arms.push(MatchArm { pat, body });
        }
        self.expect(&PTokKind::Dedent, "end of match block")?;
        Ok(Stmt::Match {
            id: 0,
            expr,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_and()?;
        while self.eat_kw("or") {
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
        let mut left = self.parse_not()?;
        while self.eat_kw("and") {
            let right = self.parse_not()?;
            left = Expr::Binary {
                op: BinOp::And,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_not(&mut self) -> Result<Expr, Diagnostic> {
        if self.eat_kw("not") {
            let inner = self.parse_not()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Not,
                expr: Box::new(inner),
            });
        }
        self.parse_cmp()
    }

    fn parse_cmp(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_add()?;
        loop {
            if self.eat_kw("in") {
                let haystack = self.parse_add()?;
                left = Expr::intrinsic(Intrinsic::Contains {
                    haystack,
                    needle: left,
                });
                continue;
            }
            if matches!(self.peek_kind(), Some(PTokKind::Ident(s)) if s == "not")
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(PTokKind::Ident(s)) if s == "in"
                )
            {
                self.next();
                self.next();
                let haystack = self.parse_add()?;
                left = Expr::Unary {
                    op: UnaryOp::Not,
                    expr: Box::new(Expr::intrinsic(Intrinsic::Contains {
                        haystack,
                        needle: left,
                    })),
                };
                continue;
            }

            let op = match self.peek_kind() {
                Some(PTokKind::EqEq) => Some(BinOp::Eq),
                Some(PTokKind::BangEq) => Some(BinOp::Ne),
                Some(PTokKind::Lt) => Some(BinOp::Lt),
                Some(PTokKind::Le) => Some(BinOp::Le),
                Some(PTokKind::Gt) => Some(BinOp::Gt),
                Some(PTokKind::Ge) => Some(BinOp::Ge),
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
                Some(PTokKind::Plus) => Some(BinOp::Add),
                Some(PTokKind::Minus) => Some(BinOp::Sub),
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
                Some(PTokKind::Star) => Some(BinOp::Mul),
                Some(PTokKind::Slash) => Some(BinOp::Div),
                Some(PTokKind::SlashSlash) => Some(BinOp::IntDiv),
                Some(PTokKind::Percent) => Some(BinOp::Mod),
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
        if self.eat(&PTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut base = self.parse_primary()?;
        loop {
            if self.eat(&PTokKind::Dot) {
                let member = self.expect_ident()?;
                if self.eat(&PTokKind::LParen) {
                    let args = self.parse_expr_list(&PTokKind::RParen)?;
                    base = match (member.as_str(), args.len()) {
                        ("append", 1) => Expr::intrinsic(Intrinsic::Push {
                            list: base,
                            value: args.into_iter().next().unwrap(),
                        }),
                        ("upper", 0) => Expr::intrinsic(Intrinsic::Upper(base)),
                        ("lower", 0) => Expr::intrinsic(Intrinsic::Lower(base)),
                        _ => {
                            return self.err(format!(
                                "unsupported Python method '.{}(...)'",
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
            } else if self.eat(&PTokKind::LBracket) {
                let idx = self.parse_expr()?;
                self.expect(&PTokKind::RBracket, "']'")?;
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
            Some(PTokKind::Int(v)) => {
                self.next();
                Ok(Expr::Int(v))
            }
            Some(PTokKind::Float(v)) => {
                self.next();
                Ok(Expr::Float(v))
            }
            Some(PTokKind::Str(s)) => {
                self.next();
                Ok(Expr::Str(s))
            }
            Some(PTokKind::LParen) => {
                self.next();
                let e = self.parse_expr()?;
                self.expect(&PTokKind::RParen, "')'")?;
                Ok(e)
            }
            Some(PTokKind::LBracket) => {
                self.next();
                let items = self.parse_expr_list(&PTokKind::RBracket)?;
                Ok(Expr::List(items))
            }
            Some(PTokKind::Ident(ident)) => {
                self.next();
                if ident == "True" {
                    return Ok(Expr::Bool(true));
                }
                if ident == "False" {
                    return Ok(Expr::Bool(false));
                }
                if self.eat(&PTokKind::LParen) {
                    if self.is_struct_call(&ident) {
                        let fields = self.parse_struct_call_args(&ident)?;
                        return Ok(Expr::StructInit {
                            name: ident,
                            fields,
                        });
                    }
                    let mut args = self.parse_expr_list(&PTokKind::RParen)?;
                    return match (ident.as_str(), args.len()) {
                        ("len", 1) => Ok(Expr::intrinsic(Intrinsic::Len(args.pop().unwrap()))),
                        ("abs", 1) => Ok(Expr::intrinsic(Intrinsic::Abs(args.pop().unwrap()))),
                        ("str", 1) => Ok(Expr::intrinsic(Intrinsic::ToStr(args.pop().unwrap()))),
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
                        ("print", _) => Ok(Expr::intrinsic(Intrinsic::Print(args))),
                        _ => Ok(Expr::Call { func: ident, args }),
                    };
                }
                Ok(Expr::Var(ident))
            }
            _ => self.err("expected Python expression"),
        }
    }

    fn is_struct_call(&self, name: &str) -> bool {
        if self.known_structs.contains_key(name) {
            return true;
        }
        let starts_upper = name
            .chars()
            .next()
            .map(|c| c.is_ascii_uppercase())
            .unwrap_or(false);
        let has_kwarg = matches!(self.peek_kind(), Some(PTokKind::Ident(_)))
            && matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(PTokKind::Eq)
            );
        starts_upper && has_kwarg
    }

    fn parse_struct_call_args(&mut self, sname: &str) -> Result<Vec<(String, Expr)>, Diagnostic> {
        let mut fields = Vec::new();
        let known_names = self.known_structs.get(sname).cloned().unwrap_or_default();
        let mut idx = 0;
        while !matches!(self.peek_kind(), Some(PTokKind::RParen) | None) {
            if matches!(self.peek_kind(), Some(PTokKind::Ident(_)))
                && matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(PTokKind::Eq)
                )
            {
                let fname = self.expect_ident()?;
                self.expect(&PTokKind::Eq, "'='")?;
                let val = self.parse_expr()?;
                fields.push((fname, val));
            } else {
                let val = self.parse_expr()?;
                let fname = known_names
                    .get(idx)
                    .cloned()
                    .unwrap_or_else(|| format!("field_{}", idx));
                fields.push((fname, val));
            }
            idx += 1;
            if !self.eat(&PTokKind::Comma) {
                break;
            }
        }
        self.expect(&PTokKind::RParen, "')'")?;
        Ok(fields)
    }

    fn parse_expr_list(&mut self, closing: &PTokKind) -> Result<Vec<Expr>, Diagnostic> {
        let mut items = Vec::new();
        while self.peek_kind() != Some(closing) && self.peek().is_some() {
            items.push(self.parse_expr()?);
            if !self.eat(&PTokKind::Comma) {
                break;
            }
        }
        self.expect(closing, "closing ')' or ']'")?;
        Ok(items)
    }
}

fn py_expr_to_target(expr: Expr) -> Result<AssignTarget, Diagnostic> {
    match expr {
        Expr::Var(v) => Ok(AssignTarget::Var(v)),
        Expr::FieldAccess { base, field } => {
            if let Expr::Var(b) = *base {
                Ok(AssignTarget::Field { base: b, field })
            } else {
                Err(Diagnostic::new(
                    "python",
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
                    "python",
                    "nested index assignment not supported",
                    1,
                    1,
                ))
            }
        }
        _ => Err(Diagnostic::new("python", "invalid assignment target", 1, 1)),
    }
}

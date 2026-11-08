use std::collections::{HashMap, HashSet};

use crate::hub::{
    AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl, HubModule, Intrinsic,
    Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl, Type, UnaryOp,
};
use crate::lens::{format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;

pub struct RubyLens;

impl LanguageLens for RubyLens {
    fn id(&self) -> SpokeId {
        SpokeId::Ruby
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut out = String::new();

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
            out.push_str("if __FILE__ == $0\n  main()\nend\n");
        } else if !out.ends_with('\n') && !out.is_empty() {
            out.push('\n');
        }
        out
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_ruby(source)?;
        let mut struct_field_order: HashMap<String, Vec<String>> = HashMap::new();
        let mut known_enums: HashSet<String> = HashSet::new();

        for item in &prev_hub.items {
            match item {
                Item::Struct(s) => {
                    struct_field_order.insert(
                        s.name.clone(),
                        s.fields.iter().map(|f| f.name.clone()).collect(),
                    );
                }
                Item::Enum(e) => {
                    known_enums.insert(e.name.clone());
                }
                _ => {}
            }
        }

        prescan_ruby_types(&tokens, &mut struct_field_order, &mut known_enums);

        let mut parser = RubyParser {
            tokens,
            pos: 0,
            struct_field_order,
            known_enums,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Ruby))
    }
}

fn escape_ruby_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '#' => out.push_str("\\#"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            other => out.push(other),
        }
    }
    out
}

fn unescape_ruby_str(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    let mut chars = raw.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some('r') => out.push('\r'),
                Some('\\') => out.push('\\'),
                Some('"') => out.push('"'),
                Some('\'') => out.push('\''),
                Some('#') => out.push('#'),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

fn fmt_rbs_type(ty: &Type) -> String {
    match ty {
        Type::Int => "Integer".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "bool".to_string(),
        Type::Str => "String".to_string(),
        Type::Void => "void".to_string(),
        Type::List(inner) => format!("Array[{}]", fmt_rbs_type(inner)),
        Type::Named(name) => name.clone(),
    }
}

fn fmt_struct(s: &StructDecl, out: &mut String) {
    for c in &s.comments {
        out.push_str(&format!("# {}\n", c));
    }
    let field_tys: Vec<String> = s
        .fields
        .iter()
        .map(|f| format!("{}: {}", f.name, fmt_rbs_type(&f.ty)))
        .collect();
    out.push_str(&format!("#: fields({})\n", field_tys.join(", ")));

    if s.fields.is_empty() {
        out.push_str(&format!(
            "class {}\n  def ==(other)\n    other.is_a?({})\n  end\nend",
            s.name, s.name
        ));
    } else {
        let syms: Vec<String> = s.fields.iter().map(|f| format!(":{}", f.name)).collect();
        out.push_str(&format!(
            "{} = Struct.new({}, keyword_init: true)",
            s.name,
            syms.join(", ")
        ));
    }
}

fn fmt_enum(e: &EnumDecl, out: &mut String) {
    for c in &e.comments {
        out.push_str(&format!("# {}\n", c));
    }
    out.push_str(&format!("module {}\n", e.name));
    for (i, v) in e.variants.iter().enumerate() {
        out.push_str(&format!("  {} = {}\n", v, i));
    }
    out.push_str("end");
}

fn fmt_fn(f: &FnDecl, out: &mut String) {
    for c in &f.comments {
        out.push_str(&format!("# {}\n", c));
    }
    let sig_params: Vec<String> = f
        .params
        .iter()
        .map(|p| format!("{}: {}", p.name, fmt_rbs_type(&p.ty)))
        .collect();
    out.push_str(&format!(
        "#: ({}) -> {}\n",
        sig_params.join(", "),
        fmt_rbs_type(&f.ret_ty)
    ));

    let param_names: Vec<&str> = f.params.iter().map(|p| p.name.as_str()).collect();
    out.push_str(&format!("def {}({})\n", f.name, param_names.join(", ")));
    for stmt in &f.body {
        fmt_stmt(stmt, 1, out);
    }
    out.push_str("end");
}

fn fmt_test(t: &TestDecl, out: &mut String) {
    for c in &t.comments {
        out.push_str(&format!("# {}\n", c));
    }
    out.push_str(&format!("def test_{}()\n", t.name));
    for stmt in &t.body {
        fmt_stmt(stmt, 1, out);
    }
    out.push_str("end");
}

fn fmt_pat(pat: &MatchPat) -> String {
    match pat {
        MatchPat::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
        MatchPat::Int(v) => v.to_string(),
        MatchPat::Str(s) => format!("\"{}\"", escape_ruby_str(s)),
        MatchPat::Wildcard => "_".to_string(),
    }
}

fn fmt_stmt(stmt: &Stmt, indent: usize, out: &mut String) {
    let pad = "  ".repeat(indent);
    match stmt {
        Stmt::Comment { text, .. } => {
            out.push_str(&format!("{}# {}\n", pad, text));
        }
        Stmt::Let {
            name, ty, value, ..
        } => {
            if let Some(t) = ty {
                out.push_str(&format!(
                    "{}{} = {} #: {}\n",
                    pad,
                    name,
                    fmt_expr(value),
                    fmt_rbs_type(t)
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
            out.push_str(&format!("{}case {}\n", pad, fmt_expr(expr)));
            for arm in arms {
                if arm.pat == MatchPat::Wildcard {
                    out.push_str(&format!("{}else\n", pad));
                } else {
                    out.push_str(&format!("{}when {}\n", pad, fmt_pat(&arm.pat)));
                }
                for s in &arm.body {
                    fmt_stmt(s, indent + 1, out);
                }
            }
            out.push_str(&format!("{}end\n", pad));
        }
        Stmt::While { cond, body, .. } => {
            out.push_str(&format!("{}while {}\n", pad, fmt_expr(cond)));
            for s in body {
                fmt_stmt(s, indent + 1, out);
            }
            out.push_str(&format!("{}end\n", pad));
        }
        Stmt::ForEach {
            var, iter, body, ..
        } => {
            out.push_str(&format!("{}for {} in {}\n", pad, var, fmt_expr(iter)));
            for s in body {
                fmt_stmt(s, indent + 1, out);
            }
            out.push_str(&format!("{}end\n", pad));
        }
        Stmt::ForRange {
            var,
            start,
            end,
            body,
            ..
        } => {
            out.push_str(&format!(
                "{}for {} in ({})...({})\n",
                pad,
                var,
                fmt_expr(start),
                fmt_expr(end)
            ));
            for s in body {
                fmt_stmt(s, indent + 1, out);
            }
            out.push_str(&format!("{}end\n", pad));
        }
        Stmt::Break { .. } => {
            out.push_str(&format!("{}break\n", pad));
        }
        Stmt::Continue { .. } => {
            out.push_str(&format!("{}next\n", pad));
        }
        Stmt::Return { value, .. } => match value {
            Some(v) => out.push_str(&format!("{}return {}\n", pad, fmt_expr(v))),
            None => out.push_str(&format!("{}return\n", pad)),
        },
        Stmt::Assert { cond, .. } => {
            out.push_str(&format!(
                "{}raise \"assert failed\" unless ({})\n",
                pad,
                fmt_expr(cond)
            ));
        }
        Stmt::AssertEq { left, right, .. } => {
            out.push_str(&format!(
                "{}raise \"assert_eq failed\" unless ({}) == ({})\n",
                pad,
                fmt_expr(left),
                fmt_expr(right)
            ));
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
    let pad = "  ".repeat(indent);
    if first {
        out.push_str(&format!("{}if {}\n", pad, fmt_expr(cond)));
    } else {
        out.push_str(&format!("{}elsif {}\n", pad, fmt_expr(cond)));
    }
    for s in then_body {
        fmt_stmt(s, indent + 1, out);
    }

    if else_body.len() == 1 && matches!(&else_body[0], Stmt::If { .. }) {
        if let Stmt::If {
            cond: c2,
            then_body: t2,
            else_body: e2,
            ..
        } = &else_body[0]
        {
            fmt_if_chain(c2, t2, e2, indent, false, out);
            return;
        }
    } else if !else_body.is_empty() {
        out.push_str(&format!("{}else\n", pad));
        for s in else_body {
            fmt_stmt(s, indent + 1, out);
        }
    }
    out.push_str(&format!("{}end\n", pad));
}

fn fmt_postfix(expr: &Expr) -> String {
    let s = fmt_expr(expr);
    match expr {
        Expr::Binary { .. } | Expr::Unary { .. } => format!("({})", s),
        _ => s,
    }
}

fn fmt_expr(expr: &Expr) -> String {
    match expr {
        Expr::Int(v) => v.to_string(),
        Expr::Float(v) => format_float(*v),
        Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        Expr::Str(s) => format!("\"{}\"", escape_ruby_str(s)),
        Expr::Var(v) => v.clone(),
        Expr::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
        Expr::List(items) => {
            let inner: Vec<String> = items.iter().map(fmt_expr).collect();
            format!("[{}]", inner.join(", "))
        }
        Expr::StructInit { name, fields } => {
            let inner: Vec<String> = fields
                .iter()
                .map(|(fname, fval)| format!("{}: {}", fname, fmt_expr(fval)))
                .collect();
            format!("{}.new({})", name, inner.join(", "))
        }
        Expr::FieldAccess { base, field } => format!("{}.{}", fmt_postfix(base), field),
        Expr::Index { base, index } => format!("{}[{}]", fmt_postfix(base), fmt_expr(index)),
        Expr::Unary { op, expr: inner } => match op {
            UnaryOp::Neg => match inner.as_ref() {
                Expr::Binary { .. } | Expr::Unary { .. } => format!("-({})", fmt_expr(inner)),
                _ => format!("-{}", fmt_expr(inner)),
            },
            UnaryOp::Not => match inner.as_ref() {
                Expr::Binary { .. } | Expr::Unary { .. } => format!("!({})", fmt_expr(inner)),
                _ => format!("!{}", fmt_expr(inner)),
            },
        },
        Expr::Binary { op, left, right } => {
            let l_str = if needs_parens(left, *op, false) {
                format!("({})", fmt_expr(left))
            } else {
                fmt_expr(left)
            };
            let r_str = if needs_parens(right, *op, true) {
                format!("({})", fmt_expr(right))
            } else {
                fmt_expr(right)
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
            let inner: Vec<String> = args.iter().map(fmt_expr).collect();
            format!("{}({})", func, inner.join(", "))
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(e) => format!("{}.length", fmt_postfix(e)),
            Intrinsic::Min(a, b) => format!("[{}, {}].min", fmt_expr(a), fmt_expr(b)),
            Intrinsic::Max(a, b) => format!("[{}, {}].max", fmt_expr(a), fmt_expr(b)),
            Intrinsic::Abs(a) => format!("{}.abs", fmt_postfix(a)),
            Intrinsic::Push { list, value } => {
                format!("{}.push({})", fmt_postfix(list), fmt_expr(value))
            }
            Intrinsic::Print(args) => {
                if args.is_empty() {
                    "puts()".to_string()
                } else if args.len() == 1 {
                    format!("puts({})", fmt_expr(&args[0]))
                } else {
                    let inner: Vec<String> = args.iter().map(fmt_expr).collect();
                    format!("puts([{}].join(\" \"))", inner.join(", "))
                }
            }
            Intrinsic::Contains { haystack, needle } => {
                format!("{}.include?({})", fmt_postfix(haystack), fmt_expr(needle))
            }
            Intrinsic::Upper(e) => format!("{}.upcase", fmt_postfix(e)),
            Intrinsic::Lower(e) => format!("{}.downcase", fmt_postfix(e)),
            Intrinsic::ToStr(e) => format!("{}.to_s", fmt_postfix(e)),
        },
    }
}

// ============================================================================
// Ruby Lexer + RBS Inline Type Comment Parser
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
enum RbTokKind {
    Ident(String),
    Symbol(String),
    Int(i64),
    Float(f64),
    Str(String),
    Comment(String),
    TypeAnnot(String),
    Newline,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Colon,
    ColonColon,
    Dot,
    DotDot,
    DotDotDot,
    Semi,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusEq,
    MinusEq,
    Eq,
    EqEq,
    Bang,
    BangEq,
    Lt,
    Le,
    Shl,
    Gt,
    Ge,
    AmpAmp,
    PipePipe,
}

#[derive(Debug, Clone)]
struct RbTok {
    kind: RbTokKind,
    line: usize,
    col: usize,
}

fn lex_ruby(src: &str) -> Result<Vec<RbTok>, Diagnostic> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut line = 1usize;
    let mut col = 1usize;

    while i < n {
        let ch = chars[i];
        if ch == ' ' || ch == '\t' || ch == '\r' {
            i += 1;
            col += 1;
            continue;
        }
        if ch == '\n' {
            if !matches!(tokens.last().map(|t: &RbTok| &t.kind), Some(RbTokKind::Newline) | None) {
                tokens.push(RbTok {
                    kind: RbTokKind::Newline,
                    line,
                    col,
                });
            }
            i += 1;
            line += 1;
            col = 1;
            continue;
        }
        if ch == '#' {
            let start_col = col;
            i += 1;
            col += 1;
            let is_rbs = i < n && chars[i] == ':';
            if is_rbs {
                i += 1;
                col += 1;
            }
            let start = i;
            while i < n && chars[i] != '\n' {
                i += 1;
                col += 1;
            }
            let raw: String = chars[start..i].iter().collect();
            let text = raw.trim().to_string();
            tokens.push(RbTok {
                kind: if is_rbs {
                    RbTokKind::TypeAnnot(text)
                } else {
                    RbTokKind::Comment(text)
                },
                line,
                col: start_col,
            });
            continue;
        }

        if ch == '"' || ch == '\'' {
            let quote = ch;
            let start_col = col;
            i += 1;
            col += 1;
            let mut raw = String::new();
            let mut closed = false;
            while i < n {
                if chars[i] == '\\' && i + 1 < n {
                    raw.push('\\');
                    raw.push(chars[i + 1]);
                    i += 2;
                    col += 2;
                    continue;
                }
                if chars[i] == quote {
                    i += 1;
                    col += 1;
                    closed = true;
                    break;
                }
                if chars[i] == '\n' {
                    break;
                }
                raw.push(chars[i]);
                i += 1;
                col += 1;
            }
            if !closed {
                return Err(Diagnostic::new(
                    "ruby",
                    "unterminated string literal",
                    line,
                    start_col,
                ));
            }
            tokens.push(RbTok {
                kind: RbTokKind::Str(unescape_ruby_str(&raw)),
                line,
                col: start_col,
            });
            continue;
        }

        // Ruby `$0` global inside `if __FILE__ == $0`
        if ch == '$' && i + 1 < n && (chars[i + 1].is_ascii_alphanumeric() || chars[i + 1] == '_') {
            let start_col = col;
            let start = i;
            i += 1;
            col += 1;
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            let name: String = chars[start..i].iter().collect();
            tokens.push(RbTok {
                kind: RbTokKind::Ident(name),
                line,
                col: start_col,
            });
            continue;
        }

        if ch.is_ascii_digit() {
            let start_col = col;
            let start = i;
            let mut is_float = false;
            while i < n && (chars[i].is_ascii_digit() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            if i + 1 < n && chars[i] == '.' && chars[i + 1].is_ascii_digit() {
                is_float = true;
                i += 1;
                col += 1;
                while i < n && (chars[i].is_ascii_digit() || chars[i] == '_') {
                    i += 1;
                    col += 1;
                }
            }
            let text: String = chars[start..i].iter().filter(|c| **c != '_').collect();
            if is_float {
                let v = text.parse::<f64>().map_err(|_| {
                    Diagnostic::new("ruby", "invalid float literal", line, start_col)
                })?;
                tokens.push(RbTok {
                    kind: RbTokKind::Float(v),
                    line,
                    col: start_col,
                });
            } else {
                let v = text.parse::<i64>().map_err(|_| {
                    Diagnostic::new("ruby", "invalid integer literal", line, start_col)
                })?;
                tokens.push(RbTok {
                    kind: RbTokKind::Int(v),
                    line,
                    col: start_col,
                });
            }
            continue;
        }

        // Ruby `:symbol` vs `::` vs `key:`
        if ch == ':' {
            let start_col = col;
            if i + 1 < n && chars[i + 1] == ':' {
                tokens.push(RbTok {
                    kind: RbTokKind::ColonColon,
                    line,
                    col: start_col,
                });
                i += 2;
                col += 2;
                continue;
            }
            if i + 1 < n && (chars[i + 1].is_ascii_alphabetic() || chars[i + 1] == '_') {
                i += 1;
                col += 1;
                let s_start = i;
                while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                    i += 1;
                    col += 1;
                }
                let sym: String = chars[s_start..i].iter().collect();
                tokens.push(RbTok {
                    kind: RbTokKind::Symbol(sym),
                    line,
                    col: start_col,
                });
                continue;
            }
            tokens.push(RbTok {
                kind: RbTokKind::Colon,
                line,
                col: start_col,
            });
            i += 1;
            col += 1;
            continue;
        }

        if ch.is_ascii_alphabetic() || ch == '_' {
            let start_col = col;
            let start = i;
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            // Allow trailing `?` or `!` on Ruby predicate/mutator methods (e.g. `include?`, `is_a?`)
            if i < n && (chars[i] == '?' || chars[i] == '!') && !(i + 1 < n && chars[i + 1] == '=') {
                i += 1;
                col += 1;
            }
            let ident: String = chars[start..i].iter().collect();
            tokens.push(RbTok {
                kind: RbTokKind::Ident(ident),
                line,
                col: start_col,
            });
            continue;
        }

        let start_col = col;
        let next_ch = chars.get(i + 1).copied();
        let next2_ch = chars.get(i + 2).copied();
        let (kind, step) = match (ch, next_ch, next2_ch) {
            ('.', Some('.'), Some('.')) => (RbTokKind::DotDotDot, 3),
            ('.', Some('.'), _) => (RbTokKind::DotDot, 2),
            ('+', Some('='), _) => (RbTokKind::PlusEq, 2),
            ('-', Some('='), _) => (RbTokKind::MinusEq, 2),
            ('=', Some('='), _) => (RbTokKind::EqEq, 2),
            ('!', Some('='), _) => (RbTokKind::BangEq, 2),
            ('<', Some('='), _) => (RbTokKind::Le, 2),
            ('<', Some('<'), _) => (RbTokKind::Shl, 2),
            ('>', Some('='), _) => (RbTokKind::Ge, 2),
            ('&', Some('&'), _) => (RbTokKind::AmpAmp, 2),
            ('|', Some('|'), _) => (RbTokKind::PipePipe, 2),
            ('(', _, _) => (RbTokKind::LParen, 1),
            (')', _, _) => (RbTokKind::RParen, 1),
            ('[', _, _) => (RbTokKind::LBracket, 1),
            (']', _, _) => (RbTokKind::RBracket, 1),
            (',', _, _) => (RbTokKind::Comma, 1),
            ('.', _, _) => (RbTokKind::Dot, 1),
            (';', _, _) => (RbTokKind::Semi, 1),
            ('+', _, _) => (RbTokKind::Plus, 1),
            ('-', _, _) => (RbTokKind::Minus, 1),
            ('*', _, _) => (RbTokKind::Star, 1),
            ('/', _, _) => (RbTokKind::Slash, 1),
            ('%', _, _) => (RbTokKind::Percent, 1),
            ('=', _, _) => (RbTokKind::Eq, 1),
            ('!', _, _) => (RbTokKind::Bang, 1),
            ('<', _, _) => (RbTokKind::Lt, 1),
            ('>', _, _) => (RbTokKind::Gt, 1),
            _ => {
                return Err(Diagnostic::new(
                    "ruby",
                    format!("unexpected character '{}'", ch),
                    line,
                    start_col,
                ))
            }
        };
        tokens.push(RbTok {
            kind,
            line,
            col: start_col,
        });
        i += step;
        col += step;
    }

    Ok(tokens)
}

fn prescan_ruby_types(
    tokens: &[RbTok],
    struct_field_order: &mut HashMap<String, Vec<String>>,
    known_enums: &mut HashSet<String>,
) {
    let mut i = 0;
    while i < tokens.len() {
        if let RbTokKind::Ident(s) = &tokens[i].kind {
            if s == "module" {
                if let Some(RbTok {
                    kind: RbTokKind::Ident(ename),
                    ..
                }) = tokens.get(i + 1)
                {
                    known_enums.insert(ename.clone());
                }
            }
            // `Summary = Struct.new(:count, :total, ...)`
            if s.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false)
                && matches!(tokens.get(i + 1).map(|t| &t.kind), Some(RbTokKind::Eq))
                && matches!(tokens.get(i + 2).map(|t| &t.kind), Some(RbTokKind::Ident(st)) if st == "Struct")
                && matches!(tokens.get(i + 3).map(|t| &t.kind), Some(RbTokKind::Dot))
                && matches!(tokens.get(i + 4).map(|t| &t.kind), Some(RbTokKind::Ident(nw)) if nw == "new")
                && matches!(tokens.get(i + 5).map(|t| &t.kind), Some(RbTokKind::LParen))
            {
                let sname = s.clone();
                let mut fields = Vec::new();
                let mut k = i + 6;
                while k < tokens.len() && !matches!(tokens[k].kind, RbTokKind::RParen) {
                    if let RbTokKind::Symbol(fname) = &tokens[k].kind {
                        fields.push(fname.clone());
                    }
                    k += 1;
                }
                struct_field_order.insert(sname, fields);
            }
        }
        i += 1;
    }
}

// ============================================================================
// RBS Inline Signature Helpers
// ============================================================================

fn parse_rbs_type_str(s: &str, line: usize, col: usize) -> Result<Type, Diagnostic> {
    let t = s.trim();
    if let Some(rest) = t.strip_prefix("Array[") {
        let inner = rest.strip_suffix(']').ok_or_else(|| {
            Diagnostic::new("ruby", format!("malformed Array[...] RBS type '{}'", t), line, col)
        })?;
        return Ok(Type::list(parse_rbs_type_str(inner, line, col)?));
    }
    match t {
        "Integer" | "int" => Ok(Type::Int),
        "Float" | "float" => Ok(Type::Float),
        "bool" | "Boolean" => Ok(Type::Bool),
        "String" | "str" => Ok(Type::Str),
        "void" | "nil" | " untyped" => Ok(Type::Void),
        other if !other.is_empty() => Ok(Type::Named(other.to_string())),
        _ => Err(Diagnostic::new("ruby", "empty RBS type annotation", line, col)),
    }
}

fn split_top_level_commas(s: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (idx, ch) in s.char_indices() {
        match ch {
            '[' | '(' => depth += 1,
            ']' | ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                parts.push(s[start..idx].trim());
                start = idx + 1;
            }
            _ => {}
        }
    }
    let tail = s[start..].trim();
    if !tail.is_empty() {
        parts.push(tail);
    }
    parts
}

fn parse_rbs_fields_annot(
    annot: &str,
    line: usize,
    col: usize,
) -> Result<HashMap<String, Type>, Diagnostic> {
    let mut map = HashMap::new();
    let Some(rest) = annot.trim().strip_prefix("fields(") else {
        return Ok(map);
    };
    let Some(inner) = rest.strip_suffix(')') else {
        return Ok(map);
    };
    for entry in split_top_level_commas(inner) {
        if let Some((k, v)) = entry.split_once(':') {
            map.insert(
                k.trim().to_string(),
                parse_rbs_type_str(v.trim(), line, col)?,
            );
        }
    }
    Ok(map)
}

type RbsParsedSig = (HashMap<String, Type>, Vec<Type>, Type);

fn parse_rbs_fn_sig(
    annot: &str,
    line: usize,
    col: usize,
) -> Result<RbsParsedSig, Diagnostic> {
    let mut by_name = HashMap::new();
    let mut positional = Vec::new();
    let s = annot.trim();
    let Some(after_open) = s.strip_prefix('(') else {
        return Err(Diagnostic::new(
            "ruby",
            format!("expected '(...) -> Ret' in RBS signature '{}'", s),
            line,
            col,
        ));
    };
    // Find matching `)` before `->`
    let mut depth = 1usize;
    let mut close_idx = None;
    for (idx, ch) in after_open.char_indices() {
        match ch {
            '(' | '[' => depth += 1,
            ')' | ']' => {
                depth -= 1;
                if depth == 0 {
                    close_idx = Some(idx);
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(cidx) = close_idx else {
        return Err(Diagnostic::new(
            "ruby",
            "unclosed '(' in RBS function signature",
            line,
            col,
        ));
    };
    let params_part = &after_open[..cidx];
    let rest = after_open[cidx + 1..].trim();
    let ret_str = rest.strip_prefix("->").ok_or_else(|| {
        Diagnostic::new("ruby", "expected '->' in RBS function signature", line, col)
    })?;
    let ret_ty = parse_rbs_type_str(ret_str.trim(), line, col)?;

    for entry in split_top_level_commas(params_part) {
        if let Some((pname, pty_s)) = entry.split_once(':') {
            let pty = parse_rbs_type_str(pty_s.trim(), line, col)?;
            by_name.insert(pname.trim().to_string(), pty.clone());
            positional.push(pty);
        } else {
            positional.push(parse_rbs_type_str(entry, line, col)?);
        }
    }
    Ok((by_name, positional, ret_ty))
}

// ============================================================================
// Ruby Recursive-Descent Parser
// ============================================================================

struct RubyParser {
    tokens: Vec<RbTok>,
    pos: usize,
    struct_field_order: HashMap<String, Vec<String>>,
    known_enums: HashSet<String>,
}

impl RubyParser {
    fn peek(&self) -> Option<&RbTok> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&RbTokKind> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn peek_kind_at(&self, offset: usize) -> Option<&RbTokKind> {
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
    }

    fn cur_loc(&self) -> (usize, usize) {
        self.peek()
            .map(|t| (t.line, t.col))
            .or_else(|| self.tokens.last().map(|t| (t.line, t.col + 1)))
            .unwrap_or((1, 1))
    }

    fn err<T>(&self, msg: impl Into<String>) -> Result<T, Diagnostic> {
        let (l, c) = self.cur_loc();
        Err(Diagnostic::new("ruby", msg, l, c))
    }

    fn eat(&mut self, want: &RbTokKind) -> bool {
        if self.peek_kind() == Some(want) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if matches!(self.peek_kind(), Some(RbTokKind::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn is_kw(&self, kw: &str) -> bool {
        matches!(self.peek_kind(), Some(RbTokKind::Ident(s)) if s == kw)
    }

    fn expect(&mut self, want: &RbTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(want) {
            Ok(())
        } else {
            self.err(format!("expected {}", label))
        }
    }

    fn expect_ident(&mut self) -> Result<String, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(RbTokKind::Ident(s)) => {
                self.pos += 1;
                Ok(s)
            }
            _ => self.err("expected identifier"),
        }
    }

    fn skip_separators(&mut self) {
        while matches!(
            self.peek_kind(),
            Some(RbTokKind::Newline | RbTokKind::Semi)
        ) {
            self.pos += 1;
        }
    }

    fn skip_until_matching_end(&mut self) -> Result<(), Diagnostic> {
        let mut depth = 1usize;
        while depth > 0 {
            let Some(tok) = self.peek_kind().cloned() else {
                return self.err("expected 'end'");
            };
            self.pos += 1;
            if let RbTokKind::Ident(s) = tok {
                match s.as_str() {
                    "if" | "unless" | "while" | "for" | "case" | "def" | "class" | "module"
                    | "begin" | "do" => depth += 1,
                    "end" => depth -= 1,
                    _ => {}
                }
            }
        }
        Ok(())
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut module = HubModule::new();

        loop {
            self.skip_separators();
            let mut comments = Vec::new();
            let mut type_annots: Vec<(String, usize, usize)> = Vec::new();

            loop {
                match self.peek().cloned() {
                    Some(RbTok {
                        kind: RbTokKind::Comment(c),
                        ..
                    }) => {
                        self.pos += 1;
                        // Ignore `# frozen_string_literal: true` magic header if present
                        if !c.starts_with("frozen_string_literal:") {
                            comments.push(c);
                        }
                        self.skip_separators();
                    }
                    Some(RbTok {
                        kind: RbTokKind::TypeAnnot(a),
                        line,
                        col,
                    }) => {
                        self.pos += 1;
                        type_annots.push((a, line, col));
                        self.skip_separators();
                    }
                    _ => break,
                }
            }

            if self.peek().is_none() {
                break;
            }

            // Skip `if __FILE__ == $0 ... end` entrypoint guard
            if self.is_kw("if")
                && matches!(self.peek_kind_at(1), Some(RbTokKind::Ident(s)) if s == "__FILE__")
            {
                self.pos += 1;
                self.skip_until_matching_end()?;
                continue;
            }

            if self.eat_kw("module") {
                let edecl = self.parse_enum(comments)?;
                module.items.push(Item::Enum(edecl));
                continue;
            }

            if self.eat_kw("class") {
                let sdecl = self.parse_empty_class_struct(comments)?;
                module.items.push(Item::Struct(sdecl));
                continue;
            }

            if self.eat_kw("def") {
                let item = self.parse_fn_or_test(comments, &type_annots)?;
                module.items.push(item);
                continue;
            }

            // `Summary = Struct.new(:count, :total, ...)`
            if let Some(RbTokKind::Ident(name)) = self.peek_kind().cloned() {
                if name.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false)
                    && matches!(self.peek_kind_at(1), Some(RbTokKind::Eq))
                {
                    let sdecl = self.parse_struct_assign(comments, &type_annots)?;
                    module.items.push(Item::Struct(sdecl));
                    continue;
                }
            }

            return self.err("expected 'def', 'module', or 'Name = Struct.new(...)' at top level");
        }

        Ok(module)
    }

    fn parse_struct_assign(
        &mut self,
        comments: Vec<String>,
        type_annots: &[(String, usize, usize)],
    ) -> Result<StructDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&RbTokKind::Eq, "'='")?;
        let st_ident = self.expect_ident()?;
        if st_ident != "Struct" {
            return self.err("expected 'Struct.new(...)'");
        }
        self.expect(&RbTokKind::Dot, "'.'")?;
        let new_ident = self.expect_ident()?;
        if new_ident != "new" {
            return self.err("expected 'Struct.new(...)'");
        }
        self.expect(&RbTokKind::LParen, "'('")?;

        let mut field_types = HashMap::new();
        for (a, l, c) in type_annots {
            for (k, v) in parse_rbs_fields_annot(a, *l, *c)? {
                field_types.insert(k, v);
            }
        }

        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), Some(RbTokKind::RParen) | None) {
            if let Some(RbTokKind::Symbol(fname)) = self.peek_kind().cloned() {
                self.pos += 1;
                let ty = field_types.get(&fname).cloned().unwrap_or(Type::Int);
                fields.push(Field {
                    id: 0,
                    name: fname,
                    ty,
                    meta: Metadata::new(),
                });
            } else if matches!(self.peek_kind(), Some(RbTokKind::Ident(k)) if k == "keyword_init") {
                self.pos += 1;
                let _ = self.eat(&RbTokKind::Colon);
                let _ = self.expect_ident();
            } else {
                return self.err("expected ':field' symbol in Struct.new(...)");
            }
            if !self.eat(&RbTokKind::Comma) {
                break;
            }
        }
        self.expect(&RbTokKind::RParen, "')'")?;
        self.struct_field_order.insert(
            name.clone(),
            fields.iter().map(|f| f.name.clone()).collect(),
        );
        Ok(StructDecl {
            id: 0,
            name,
            fields,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_empty_class_struct(&mut self, comments: Vec<String>) -> Result<StructDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.skip_until_matching_end()?;
        self.struct_field_order.insert(name.clone(), Vec::new());
        Ok(StructDecl {
            id: 0,
            name,
            fields: Vec::new(),
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_enum(&mut self, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.known_enums.insert(name.clone());
        let mut variants = Vec::new();
        loop {
            self.skip_separators();
            if matches!(self.peek_kind(), Some(RbTokKind::Comment(_) | RbTokKind::TypeAnnot(_))) {
                self.pos += 1;
                continue;
            }
            if self.eat_kw("end") {
                break;
            }
            if self.peek().is_none() {
                return self.err("expected 'end' to close module enum");
            }
            let vname = self.expect_ident()?;
            self.expect(&RbTokKind::Eq, "'=' after enum variant")?;
            let _ = self.parse_expr()?;
            variants.push(vname);
        }
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_fn_or_test(
        &mut self,
        comments: Vec<String>,
        type_annots: &[(String, usize, usize)],
    ) -> Result<Item, Diagnostic> {
        let name = self.expect_ident()?;
        let mut param_names = Vec::new();
        if self.eat(&RbTokKind::LParen) {
            while !matches!(self.peek_kind(), Some(RbTokKind::RParen) | None) {
                param_names.push(self.expect_ident()?);
                if !self.eat(&RbTokKind::Comma) {
                    break;
                }
            }
            self.expect(&RbTokKind::RParen, "')'")?;
        }

        let mut sig_by_name = HashMap::new();
        let mut sig_pos = Vec::new();
        let mut ret_ty = Type::Void;
        if let Some((annot, l, c)) = type_annots.last() {
            let (bn, pos_tys, rty) = parse_rbs_fn_sig(annot, *l, *c)?;
            sig_by_name = bn;
            sig_pos = pos_tys;
            ret_ty = rty;
        }

        let mut scope = HashSet::new();
        let mut params = Vec::new();
        for (idx, pname) in param_names.into_iter().enumerate() {
            let pty = sig_by_name
                .get(&pname)
                .cloned()
                .or_else(|| sig_pos.get(idx).cloned())
                .unwrap_or(Type::Int);
            scope.insert(pname.clone());
            params.push(Param {
                id: 0,
                name: pname,
                ty: pty,
                meta: Metadata::new(),
            });
        }

        let body = self.parse_block_until(&["end"], &mut scope)?;
        self.expect_kw("end")?;

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

    fn expect_kw(&mut self, kw: &str) -> Result<(), Diagnostic> {
        if self.eat_kw(kw) {
            Ok(())
        } else {
            self.err(format!("expected '{}'", kw))
        }
    }

    fn at_block_terminator(&self, terminators: &[&str]) -> bool {
        match self.peek_kind() {
            None => true,
            Some(RbTokKind::Ident(s)) => terminators.contains(&s.as_str()),
            _ => false,
        }
    }

    fn parse_block_until(
        &mut self,
        terminators: &[&str],
        enclosing_scope: &mut HashSet<String>,
    ) -> Result<Vec<Stmt>, Diagnostic> {
        let mut stmts = Vec::new();
        let mut local_scope = enclosing_scope.clone();

        loop {
            self.skip_separators();
            if self.at_block_terminator(terminators) {
                break;
            }

            if let Some(RbTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.pos += 1;
                stmts.push(Stmt::Comment { id: 0, text: c });
                continue;
            }
            if matches!(self.peek_kind(), Some(RbTokKind::TypeAnnot(_))) {
                self.pos += 1;
                continue;
            }

            if self.eat_kw("if") {
                stmts.push(self.parse_if(&mut local_scope)?);
                continue;
            }
            if self.eat_kw("case") {
                stmts.push(self.parse_case(&mut local_scope)?);
                continue;
            }
            if self.eat_kw("while") {
                let cond = self.parse_expr()?;
                let _ = self.eat_kw("do");
                let body = self.parse_block_until(&["end"], &mut local_scope)?;
                self.expect_kw("end")?;
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
                self.expect_kw("in")?;
                let first_expr = self.parse_expr()?;
                if self.eat(&RbTokKind::DotDotDot) {
                    let end_expr = self.parse_expr()?;
                    let _ = self.eat_kw("do");
                    let mut loop_scope = local_scope.clone();
                    loop_scope.insert(var.clone());
                    let body = self.parse_block_until(&["end"], &mut loop_scope)?;
                    self.expect_kw("end")?;
                    stmts.push(Stmt::ForRange {
                        id: 0,
                        var,
                        start: first_expr,
                        end: end_expr,
                        body,
                        meta: Metadata::new(),
                    });
                } else {
                    let _ = self.eat_kw("do");
                    let mut loop_scope = local_scope.clone();
                    loop_scope.insert(var.clone());
                    let body = self.parse_block_until(&["end"], &mut loop_scope)?;
                    self.expect_kw("end")?;
                    stmts.push(Stmt::ForEach {
                        id: 0,
                        var,
                        iter: first_expr,
                        body,
                        meta: Metadata::new(),
                    });
                }
                continue;
            }
            if self.eat_kw("break") {
                stmts.push(Stmt::Break { id: 0 });
                continue;
            }
            if self.eat_kw("next") {
                stmts.push(Stmt::Continue { id: 0 });
                continue;
            }
            if self.eat_kw("return") {
                if matches!(
                    self.peek_kind(),
                    Some(RbTokKind::Newline | RbTokKind::Semi) | None
                ) || self.at_block_terminator(terminators)
                {
                    stmts.push(Stmt::Return {
                        id: 0,
                        value: None,
                        meta: Metadata::new(),
                    });
                } else {
                    let val = self.parse_expr()?;
                    stmts.push(Stmt::Return {
                        id: 0,
                        value: Some(val),
                        meta: Metadata::new(),
                    });
                }
                continue;
            }
            if self.eat_kw("raise") {
                stmts.push(self.parse_raise_assert()?);
                continue;
            }

            let expr = self.parse_expr()?;
            // Support `list << val` as `Intrinsic::Push`
            if self.eat(&RbTokKind::Shl) {
                let val = self.parse_expr()?;
                stmts.push(Stmt::Expr {
                    id: 0,
                    expr: Expr::intrinsic(Intrinsic::Push {
                        list: expr,
                        value: val,
                    }),
                    meta: Metadata::new(),
                });
                continue;
            }

            if let Some(op) = match self.peek_kind() {
                Some(RbTokKind::Eq) => Some(AssignOp::Set),
                Some(RbTokKind::PlusEq) => Some(AssignOp::AddAssign),
                Some(RbTokKind::MinusEq) => Some(AssignOp::SubAssign),
                _ => None,
            } {
                self.pos += 1;
                let value = self.parse_expr()?;
                let inline_ty = if let Some(RbTok {
                    kind: RbTokKind::TypeAnnot(ts),
                    line,
                    col,
                }) = self.peek().cloned()
                {
                    self.pos += 1;
                    Some(parse_rbs_type_str(&ts, line, col)?)
                } else {
                    None
                };

                if op == AssignOp::Set {
                    if let Expr::Var(vname) = &expr {
                        if !local_scope.contains(vname) {
                            local_scope.insert(vname.clone());
                            stmts.push(Stmt::Let {
                                id: 0,
                                name: vname.clone(),
                                mutable: false,
                                ty: inline_ty,
                                value,
                                meta: Metadata::new(),
                            });
                            continue;
                        }
                    }
                }

                let target = expr_to_assign_target(expr).ok_or_else(|| {
                    let (l, c) = self.cur_loc();
                    Diagnostic::new("ruby", "invalid assignment target", l, c)
                })?;
                stmts.push(Stmt::Assign {
                    id: 0,
                    target,
                    op,
                    value,
                    meta: Metadata::new(),
                });
                continue;
            }

            stmts.push(Stmt::Expr {
                id: 0,
                expr,
                meta: Metadata::new(),
            });
        }

        Ok(stmts)
    }

    fn parse_raise_assert(&mut self) -> Result<Stmt, Diagnostic> {
        let mut is_assert_eq = false;
        // Optional exception message or `RuntimeError, "msg"`
        if matches!(self.peek_kind(), Some(RbTokKind::LParen)) {
            self.pos += 1;
            if let Some(RbTokKind::Str(msg)) = self.peek_kind().cloned() {
                if msg.contains("assert_eq") {
                    is_assert_eq = true;
                }
                self.pos += 1;
            }
            self.expect(&RbTokKind::RParen, "')'")?;
        } else if let Some(RbTokKind::Str(msg)) = self.peek_kind().cloned() {
            if msg.contains("assert_eq") {
                is_assert_eq = true;
            }
            self.pos += 1;
        }

        if self.eat_kw("unless") {
            let cond = self.parse_expr()?;
            if is_assert_eq {
                if let Expr::Binary {
                    op: BinOp::Eq,
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
            }
            return Ok(Stmt::Assert {
                id: 0,
                cond,
                meta: Metadata::new(),
            });
        }

        if self.eat_kw("if") {
            let cond = self.parse_expr()?;
            if is_assert_eq {
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
                cond: Expr::Unary {
                    op: UnaryOp::Not,
                    expr: Box::new(cond),
                },
                meta: Metadata::new(),
            });
        }

        self.err("expected 'unless' or 'if' modifier after 'raise' assertion")
    }

    fn parse_if(&mut self, scope: &mut HashSet<String>) -> Result<Stmt, Diagnostic> {
        let cond = self.parse_expr()?;
        let _ = self.eat_kw("then");
        let then_body = self.parse_block_until(&["elsif", "else", "end"], scope)?;
        let else_body = if self.eat_kw("elsif") {
            vec![self.parse_if(scope)?]
        } else if self.eat_kw("else") {
            let b = self.parse_block_until(&["end"], scope)?;
            self.expect_kw("end")?;
            b
        } else {
            self.expect_kw("end")?;
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

    fn parse_case(&mut self, scope: &mut HashSet<String>) -> Result<Stmt, Diagnostic> {
        let expr = self.parse_expr()?;
        let mut arms = Vec::new();
        loop {
            self.skip_separators();
            if matches!(self.peek_kind(), Some(RbTokKind::Comment(_) | RbTokKind::TypeAnnot(_))) {
                self.pos += 1;
                continue;
            }
            if self.eat_kw("when") {
                let pat = self.parse_pat()?;
                let _ = self.eat_kw("then");
                let body = self.parse_block_until(&["when", "else", "end"], scope)?;
                arms.push(MatchArm { pat, body });
            } else if self.eat_kw("else") {
                let body = self.parse_block_until(&["end"], scope)?;
                arms.push(MatchArm {
                    pat: MatchPat::Wildcard,
                    body,
                });
            } else if self.eat_kw("end") {
                break;
            } else {
                return self.err("expected 'when', 'else', or 'end' inside 'case'");
            }
        }
        Ok(Stmt::Match {
            id: 0,
            expr,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_pat(&mut self) -> Result<MatchPat, Diagnostic> {
        if self.eat(&RbTokKind::Minus) {
            if let Some(RbTokKind::Int(v)) = self.peek_kind().cloned() {
                self.pos += 1;
                return Ok(MatchPat::Int(-v));
            }
            return self.err("expected integer literal after '-' in when pattern");
        }
        match self.peek_kind().cloned() {
            Some(RbTokKind::Int(v)) => {
                self.pos += 1;
                Ok(MatchPat::Int(v))
            }
            Some(RbTokKind::Str(s)) => {
                self.pos += 1;
                Ok(MatchPat::Str(s))
            }
            Some(RbTokKind::Ident(s)) if s == "_" => {
                self.pos += 1;
                Ok(MatchPat::Wildcard)
            }
            Some(RbTokKind::Ident(ename)) => {
                self.pos += 1;
                if self.eat(&RbTokKind::ColonColon) || self.eat(&RbTokKind::Dot) {
                    let vname = self.expect_ident()?;
                    Ok(MatchPat::EnumVariant {
                        enum_name: ename,
                        variant: vname,
                    })
                } else {
                    self.err("expected 'Enum::Variant' in when pattern")
                }
            }
            _ => self.err("expected pattern after 'when'"),
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_and()?;
        while self.eat(&RbTokKind::PipePipe) || self.eat_kw("or") {
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
        while self.eat(&RbTokKind::AmpAmp) || self.eat_kw("and") {
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
                Some(RbTokKind::EqEq) => Some(BinOp::Eq),
                Some(RbTokKind::BangEq) => Some(BinOp::Ne),
                Some(RbTokKind::Lt) => Some(BinOp::Lt),
                Some(RbTokKind::Le) => Some(BinOp::Le),
                Some(RbTokKind::Gt) => Some(BinOp::Gt),
                Some(RbTokKind::Ge) => Some(BinOp::Ge),
                _ => None,
            };
            if let Some(op) = op {
                self.pos += 1;
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
                Some(RbTokKind::Plus) => Some(BinOp::Add),
                Some(RbTokKind::Minus) => Some(BinOp::Sub),
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
                Some(RbTokKind::Star) => Some(BinOp::Mul),
                Some(RbTokKind::Slash) => Some(BinOp::Div),
                Some(RbTokKind::Percent) => Some(BinOp::Mod),
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
        if self.eat(&RbTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        if self.eat(&RbTokKind::Bang) || self.eat_kw("not") {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Not,
                expr: Box::new(inner),
            });
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut expr = self.parse_primary()?;
        loop {
            if self.eat(&RbTokKind::LBracket) {
                let idx = self.parse_expr()?;
                self.expect(&RbTokKind::RBracket, "']'")?;
                expr = Expr::Index {
                    base: Box::new(expr),
                    index: Box::new(idx),
                };
                continue;
            }
            if self.eat(&RbTokKind::Dot) {
                let method = self.expect_ident()?;

                // Struct constructor `Summary.new(count: 1, ...)`
                if method == "new" {
                    if let Expr::Var(sname) = &expr {
                        if sname
                            .chars()
                            .next()
                            .map(|c| c.is_ascii_uppercase())
                            .unwrap_or(false)
                        {
                            let struct_name = sname.clone();
                            let mut fields = Vec::new();
                            if self.eat(&RbTokKind::LParen) {
                                let mut pos_idx = 0usize;
                                while !matches!(self.peek_kind(), Some(RbTokKind::RParen) | None) {
                                    if matches!(self.peek_kind(), Some(RbTokKind::Ident(_)))
                                        && matches!(self.peek_kind_at(1), Some(RbTokKind::Colon))
                                    {
                                        let fname = self.expect_ident()?;
                                        self.expect(&RbTokKind::Colon, "':'")?;
                                        let fval = self.parse_expr()?;
                                        fields.push((fname, fval));
                                    } else {
                                        let fval = self.parse_expr()?;
                                        let fname = self
                                            .struct_field_order
                                            .get(&struct_name)
                                            .and_then(|ord| ord.get(pos_idx))
                                            .cloned()
                                            .unwrap_or_else(|| format!("field_{}", pos_idx));
                                        fields.push((fname, fval));
                                        pos_idx += 1;
                                    }
                                    if !self.eat(&RbTokKind::Comma) {
                                        break;
                                    }
                                }
                                self.expect(&RbTokKind::RParen, "')'")?;
                            }
                            expr = Expr::StructInit {
                                name: struct_name,
                                fields,
                            };
                            continue;
                        }
                    }
                }

                let mut args = Vec::new();
                let had_parens = if self.eat(&RbTokKind::LParen) {
                    while !matches!(self.peek_kind(), Some(RbTokKind::RParen) | None) {
                        args.push(self.parse_expr()?);
                        if !self.eat(&RbTokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&RbTokKind::RParen, "')'")?;
                    true
                } else {
                    false
                };

                match (method.as_str(), args.len()) {
                    ("length" | "size" | "count", 0) => {
                        expr = Expr::intrinsic(Intrinsic::Len(expr));
                    }
                    ("abs", 0) => {
                        expr = Expr::intrinsic(Intrinsic::Abs(expr));
                    }
                    ("upcase", 0) => {
                        expr = Expr::intrinsic(Intrinsic::Upper(expr));
                    }
                    ("downcase", 0) => {
                        expr = Expr::intrinsic(Intrinsic::Lower(expr));
                    }
                    ("to_s", 0) => {
                        expr = Expr::intrinsic(Intrinsic::ToStr(expr));
                    }
                    ("min", 0) => {
                        if let Expr::List(mut items) = expr {
                            if items.len() == 2 {
                                let b = items.pop().unwrap();
                                let a = items.pop().unwrap();
                                expr = Expr::intrinsic(Intrinsic::Min(a, b));
                                continue;
                            }
                            return self.err("expected 2-element array before '.min'");
                        }
                        return self.err("expected '[a, b].min'");
                    }
                    ("max", 0) => {
                        if let Expr::List(mut items) = expr {
                            if items.len() == 2 {
                                let b = items.pop().unwrap();
                                let a = items.pop().unwrap();
                                expr = Expr::intrinsic(Intrinsic::Max(a, b));
                                continue;
                            }
                            return self.err("expected 2-element array before '.max'");
                        }
                        return self.err("expected '[a, b].max'");
                    }
                    ("push" | "append", 1) => {
                        let v = args.pop().unwrap();
                        expr = Expr::intrinsic(Intrinsic::Push {
                            list: expr,
                            value: v,
                        });
                    }
                    ("include?", 1) => {
                        let needle = args.pop().unwrap();
                        expr = Expr::intrinsic(Intrinsic::Contains {
                            haystack: expr,
                            needle,
                        });
                    }
                    _ if !had_parens && args.is_empty() => {
                        expr = Expr::FieldAccess {
                            base: Box::new(expr),
                            field: method,
                        };
                    }
                    _ => {
                        return self.err(format!("unsupported Ruby method '.{}'", method));
                    }
                }
                continue;
            }
            break;
        }
        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Expr, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(RbTokKind::Int(v)) => {
                self.pos += 1;
                Ok(Expr::Int(v))
            }
            Some(RbTokKind::Float(v)) => {
                self.pos += 1;
                Ok(Expr::Float(v))
            }
            Some(RbTokKind::Str(s)) => {
                self.pos += 1;
                Ok(Expr::Str(s))
            }
            Some(RbTokKind::LParen) => {
                self.pos += 1;
                let inner = self.parse_expr()?;
                self.expect(&RbTokKind::RParen, "')'")?;
                Ok(inner)
            }
            Some(RbTokKind::LBracket) => {
                self.pos += 1;
                let mut items = Vec::new();
                while !matches!(self.peek_kind(), Some(RbTokKind::RBracket) | None) {
                    self.skip_separators();
                    if matches!(self.peek_kind(), Some(RbTokKind::RBracket) | None) {
                        break;
                    }
                    items.push(self.parse_expr()?);
                    self.skip_separators();
                    if !self.eat(&RbTokKind::Comma) {
                        break;
                    }
                }
                self.expect(&RbTokKind::RBracket, "']'")?;
                Ok(Expr::List(items))
            }
            Some(RbTokKind::Ident(s)) if s == "true" => {
                self.pos += 1;
                Ok(Expr::Bool(true))
            }
            Some(RbTokKind::Ident(s)) if s == "false" => {
                self.pos += 1;
                Ok(Expr::Bool(false))
            }
            Some(RbTokKind::Ident(ident)) => {
                self.pos += 1;

                // `Enum::Variant`
                if self.eat(&RbTokKind::ColonColon) {
                    let variant = self.expect_ident()?;
                    return Ok(Expr::EnumVariant {
                        enum_name: ident,
                        variant,
                    });
                }

                // `puts(...)` or unparenthesized `puts a, b`
                if ident == "puts" {
                    let args = self.parse_puts_args()?;
                    return Ok(Expr::intrinsic(Intrinsic::Print(args)));
                }

                // Function call `foo(...)`
                if self.eat(&RbTokKind::LParen) {
                    let mut args = Vec::new();
                    while !matches!(self.peek_kind(), Some(RbTokKind::RParen) | None) {
                        args.push(self.parse_expr()?);
                        if !self.eat(&RbTokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&RbTokKind::RParen, "')'")?;
                    return Ok(Expr::Call { func: ident, args });
                }

                Ok(Expr::Var(ident))
            }
            _ => self.err("expected expression"),
        }
    }

    fn parse_puts_args(&mut self) -> Result<Vec<Expr>, Diagnostic> {
        if self.eat(&RbTokKind::LParen) {
            if self.eat(&RbTokKind::RParen) {
                return Ok(Vec::new());
            }
            // Check special `[a, b, ...].join(" ")` emitted for multi-arg Print
            if matches!(self.peek_kind(), Some(RbTokKind::LBracket)) {
                let saved = self.pos;
                if let Ok(Expr::List(items)) = self.parse_primary() {
                    if self.eat(&RbTokKind::Dot)
                        && matches!(self.peek_kind(), Some(RbTokKind::Ident(m)) if m == "join")
                        && matches!(self.peek_kind_at(1), Some(RbTokKind::LParen))
                        && matches!(self.peek_kind_at(2), Some(RbTokKind::Str(sep)) if sep == " ")
                        && matches!(self.peek_kind_at(3), Some(RbTokKind::RParen))
                        && matches!(self.peek_kind_at(4), Some(RbTokKind::RParen))
                    {
                        self.pos += 5;
                        return Ok(items);
                    }
                }
                self.pos = saved;
            }

            let mut args = Vec::new();
            while !matches!(self.peek_kind(), Some(RbTokKind::RParen) | None) {
                args.push(self.parse_expr()?);
                if !self.eat(&RbTokKind::Comma) {
                    break;
                }
            }
            self.expect(&RbTokKind::RParen, "')'")?;
            return Ok(args);
        }

        // Unparenthesized `puts a, b`
        if matches!(
            self.peek_kind(),
            Some(RbTokKind::Newline | RbTokKind::Semi) | None
        ) {
            return Ok(Vec::new());
        }
        let mut args = Vec::new();
        args.push(self.parse_expr()?);
        while self.eat(&RbTokKind::Comma) {
            args.push(self.parse_expr()?);
        }
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

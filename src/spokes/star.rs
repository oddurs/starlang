use crate::hub::{
    AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl, HubModule, Intrinsic,
    Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl, Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct StarLens;

impl LanguageLens for StarLens {
    fn id(&self) -> SpokeId {
        SpokeId::Star
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut out = String::new();
        out.push_str(";; Star Canonical Hub S-Expression\n");
        for (idx, item) in hub.items.iter().enumerate() {
            if idx > 0 {
                out.push('\n');
            }
            match item {
                Item::Struct(s) => fmt_struct(s, &mut out),
                Item::Enum(e) => fmt_enum(e, &mut out),
                Item::Function(f) => fmt_fn(f, &mut out),
                Item::Test(t) => fmt_test(t, &mut out),
            }
        }
        out
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_sexpr(source)?;
        let mut parser = SExprParser { tokens, pos: 0 };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Star))
    }
}

fn fmt_meta(meta: &Metadata, out: &mut String) {
    for (k, v) in meta {
        out.push_str(&format!(" :{} \"{}\"", k, escape_str(v)));
    }
}

fn fmt_type(ty: &Type) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Str => "Str".to_string(),
        Type::Void => "Void".to_string(),
        Type::List(inner) => format!("(List {})", fmt_type(inner)),
        Type::Named(name) => name.clone(),
    }
}

fn fmt_struct(s: &StructDecl, out: &mut String) {
    for c in &s.comments {
        out.push_str(&format!(";; {}\n", c));
    }
    out.push_str(&format!("(struct {}", s.name));
    fmt_meta(&s.meta, out);
    for f in &s.fields {
        out.push_str(&format!("\n  (field {} {}", f.name, fmt_type(&f.ty)));
        fmt_meta(&f.meta, out);
        out.push(')');
    }
    out.push_str(")\n");
}

fn fmt_enum(e: &EnumDecl, out: &mut String) {
    for c in &e.comments {
        out.push_str(&format!(";; {}\n", c));
    }
    out.push_str(&format!("(enum {}", e.name));
    fmt_meta(&e.meta, out);
    for v in &e.variants {
        out.push_str(&format!(" {}", v));
    }
    out.push_str(")\n");
}

fn fmt_fn(f: &FnDecl, out: &mut String) {
    for c in &f.comments {
        out.push_str(&format!(";; {}\n", c));
    }
    out.push_str(&format!("(fn {} (", f.name));
    for (i, p) in f.params.iter().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        out.push_str(&format!("(param {} {}", p.name, fmt_type(&p.ty)));
        fmt_meta(&p.meta, out);
        out.push(')');
    }
    out.push_str(&format!(") -> {}", fmt_type(&f.ret_ty)));
    fmt_meta(&f.meta, out);
    for stmt in &f.body {
        out.push('\n');
        fmt_stmt(stmt, 1, out);
    }
    out.push_str(")\n");
}

fn fmt_test(t: &TestDecl, out: &mut String) {
    for c in &t.comments {
        out.push_str(&format!(";; {}\n", c));
    }
    out.push_str(&format!("(test {}", t.name));
    fmt_meta(&t.meta, out);
    for stmt in &t.body {
        out.push('\n');
        fmt_stmt(stmt, 1, out);
    }
    out.push_str(")\n");
}

fn fmt_pat(pat: &MatchPat) -> String {
    match pat {
        MatchPat::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
        MatchPat::Int(v) => v.to_string(),
        MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
        MatchPat::Wildcard => "_".to_string(),
    }
}

fn fmt_stmt(stmt: &Stmt, indent: usize, out: &mut String) {
    let pad = "  ".repeat(indent);
    match stmt {
        Stmt::Comment { text, .. } => {
            out.push_str(&format!("{};; {}", pad, text));
        }
        Stmt::Let {
            name,
            mutable,
            ty,
            value,
            ..
        } => {
            let kw = if *mutable { "let-mut" } else { "let" };
            if let Some(t) = ty {
                out.push_str(&format!(
                    "{}({} {} :type {} {})",
                    pad,
                    kw,
                    name,
                    fmt_type(t),
                    fmt_expr(value)
                ));
            } else {
                out.push_str(&format!("{}({} {} {})", pad, kw, name, fmt_expr(value)));
            }
        }
        Stmt::Assign {
            target, op, value, ..
        } => {
            let head = match op {
                AssignOp::Set => "set!",
                AssignOp::AddAssign => "add!",
                AssignOp::SubAssign => "sub!",
            };
            let tgt = match target {
                AssignTarget::Var(v) => v.clone(),
                AssignTarget::Field { base, field } => format!("(field {} {})", base, field),
                AssignTarget::Index { base, index } => {
                    format!("(index {} {})", base, fmt_expr(index))
                }
            };
            out.push_str(&format!("{}({} {} {})", pad, head, tgt, fmt_expr(value)));
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            out.push_str(&format!("{}(if {}\n", pad, fmt_expr(cond)));
            out.push_str(&format!("{}  (then", pad));
            for s in then_body {
                out.push('\n');
                fmt_stmt(s, indent + 2, out);
            }
            out.push(')');
            if !else_body.is_empty() {
                out.push_str(&format!("\n{}  (else", pad));
                for s in else_body {
                    out.push('\n');
                    fmt_stmt(s, indent + 2, out);
                }
                out.push(')');
            }
            out.push(')');
        }
        Stmt::Match { expr, arms, .. } => {
            out.push_str(&format!("{}(match {}", pad, fmt_expr(expr)));
            for arm in arms {
                out.push_str(&format!("\n{}  (case {}", pad, fmt_pat(&arm.pat)));
                for s in &arm.body {
                    out.push('\n');
                    fmt_stmt(s, indent + 2, out);
                }
                out.push(')');
            }
            out.push(')');
        }
        Stmt::While { cond, body, .. } => {
            out.push_str(&format!("{}(while {}", pad, fmt_expr(cond)));
            for s in body {
                out.push('\n');
                fmt_stmt(s, indent + 1, out);
            }
            out.push(')');
        }
        Stmt::ForEach {
            var, iter, body, ..
        } => {
            out.push_str(&format!("{}(for-each {} {}", pad, var, fmt_expr(iter)));
            for s in body {
                out.push('\n');
                fmt_stmt(s, indent + 1, out);
            }
            out.push(')');
        }
        Stmt::ForRange {
            var,
            start,
            end,
            body,
            ..
        } => {
            out.push_str(&format!(
                "{}(for-range {} {} {}",
                pad,
                var,
                fmt_expr(start),
                fmt_expr(end)
            ));
            for s in body {
                out.push('\n');
                fmt_stmt(s, indent + 1, out);
            }
            out.push(')');
        }
        Stmt::Break { .. } => out.push_str(&format!("{}(break)", pad)),
        Stmt::Continue { .. } => out.push_str(&format!("{}(continue)", pad)),
        Stmt::Return { value, .. } => match value {
            Some(v) => out.push_str(&format!("{}(return {})", pad, fmt_expr(v))),
            None => out.push_str(&format!("{}(return)", pad)),
        },
        Stmt::Assert { cond, .. } => {
            out.push_str(&format!("{}(assert {})", pad, fmt_expr(cond)));
        }
        Stmt::AssertEq { left, right, .. } => {
            out.push_str(&format!(
                "{}(assert-eq {} {})",
                pad,
                fmt_expr(left),
                fmt_expr(right)
            ));
        }
        Stmt::Expr { expr, .. } => {
            out.push_str(&format!("{}{}", pad, fmt_expr(expr)));
        }
    }
}

fn fmt_expr(expr: &Expr) -> String {
    match expr {
        Expr::Int(v) => v.to_string(),
        Expr::Float(v) => format_float(*v),
        Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        Expr::Str(s) => format!("\"{}\"", escape_str(s)),
        Expr::Var(v) => v.clone(),
        Expr::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
        Expr::List(items) => {
            if items.is_empty() {
                "(list)".to_string()
            } else {
                let inner: Vec<String> = items.iter().map(fmt_expr).collect();
                format!("(list {})", inner.join(" "))
            }
        }
        Expr::StructInit { name, fields } => {
            let mut s = format!("(make {}", name);
            for (fname, fval) in fields {
                s.push_str(&format!(" ({} {})", fname, fmt_expr(fval)));
            }
            s.push(')');
            s
        }
        Expr::FieldAccess { base, field } => format!("(get-field {} {})", fmt_expr(base), field),
        Expr::Index { base, index } => format!("(index {} {})", fmt_expr(base), fmt_expr(index)),
        Expr::Unary { op, expr } => {
            let sym = match op {
                UnaryOp::Neg => "neg",
                UnaryOp::Not => "not",
            };
            format!("({} {})", sym, fmt_expr(expr))
        }
        Expr::Binary { op, left, right } => {
            let sym = match op {
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
            format!("({} {} {})", sym, fmt_expr(left), fmt_expr(right))
        }
        Expr::Call { func, args } => {
            if args.is_empty() {
                format!("(call {})", func)
            } else {
                let inner: Vec<String> = args.iter().map(fmt_expr).collect();
                format!("(call {} {})", func, inner.join(" "))
            }
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(e) => format!("(len {})", fmt_expr(e)),
            Intrinsic::Min(a, b) => format!("(min {} {})", fmt_expr(a), fmt_expr(b)),
            Intrinsic::Max(a, b) => format!("(max {} {})", fmt_expr(a), fmt_expr(b)),
            Intrinsic::Abs(a) => format!("(abs {})", fmt_expr(a)),
            Intrinsic::Push { list, value } => {
                format!("(push! {} {})", fmt_expr(list), fmt_expr(value))
            }
            Intrinsic::Print(args) => {
                if args.is_empty() {
                    "(print)".to_string()
                } else {
                    let inner: Vec<String> = args.iter().map(fmt_expr).collect();
                    format!("(print {})", inner.join(" "))
                }
            }
            Intrinsic::Contains { haystack, needle } => {
                format!("(contains {} {})", fmt_expr(haystack), fmt_expr(needle))
            }
            Intrinsic::Upper(e) => format!("(upper {})", fmt_expr(e)),
            Intrinsic::Lower(e) => format!("(lower {})", fmt_expr(e)),
            Intrinsic::ToStr(e) => format!("(to-str {})", fmt_expr(e)),
        },
    }
}

#[derive(Debug, Clone)]
enum STokKind {
    LParen,
    RParen,
    Str(String),
    Comment(String),
    Atom(String),
}

#[derive(Debug, Clone)]
struct STok {
    kind: STokKind,
    line: usize,
    col: usize,
}

fn lex_sexpr(src: &str) -> Result<Vec<STok>, Diagnostic> {
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
        if ch == ';' {
            let start_col = col;
            while i < chars.len() && chars[i] == ';' {
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
            if text != "Star Canonical Hub S-Expression" {
                tokens.push(STok {
                    kind: STokKind::Comment(text),
                    line,
                    col: start_col,
                });
            }
            continue;
        }
        if ch == '(' {
            tokens.push(STok {
                kind: STokKind::LParen,
                line,
                col,
            });
            i += 1;
            col += 1;
            continue;
        }
        if ch == ')' {
            tokens.push(STok {
                kind: STokKind::RParen,
                line,
                col,
            });
            i += 1;
            col += 1;
            continue;
        }
        if ch == '"' {
            let start_line = line;
            let start_col = col;
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
                    "star",
                    "unterminated string literal",
                    start_line,
                    start_col,
                ));
            }
            tokens.push(STok {
                kind: STokKind::Str(unescape_string(&raw)),
                line: start_line,
                col: start_col,
            });
            continue;
        }

        let start_col = col;
        let start = i;
        while i < chars.len()
            && !chars[i].is_whitespace()
            && chars[i] != '('
            && chars[i] != ')'
            && chars[i] != ';'
        {
            i += 1;
            col += 1;
        }
        let atom: String = chars[start..i].iter().collect();
        tokens.push(STok {
            kind: STokKind::Atom(atom),
            line,
            col: start_col,
        });
    }

    Ok(tokens)
}

struct SExprParser {
    tokens: Vec<STok>,
    pos: usize,
}

impl SExprParser {
    fn peek(&self) -> Option<&STok> {
        self.tokens.get(self.pos)
    }

    fn next(&mut self) -> Option<STok> {
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
        Err(Diagnostic::new("star", msg, line, col))
    }

    fn expect_lparen(&mut self) -> Result<(), Diagnostic> {
        match self.next() {
            Some(STok {
                kind: STokKind::LParen,
                ..
            }) => Ok(()),
            _ => self.err("expected '('"),
        }
    }

    fn expect_rparen(&mut self) -> Result<(), Diagnostic> {
        match self.next() {
            Some(STok {
                kind: STokKind::RParen,
                ..
            }) => Ok(()),
            _ => self.err("expected ')'"),
        }
    }

    fn expect_atom(&mut self) -> Result<String, Diagnostic> {
        match self.next() {
            Some(STok {
                kind: STokKind::Atom(s),
                ..
            }) => Ok(s),
            _ => self.err("expected identifier or symbol"),
        }
    }

    fn parse_meta(&mut self) -> Result<Metadata, Diagnostic> {
        let mut meta = Metadata::new();
        while let Some(STok {
            kind: STokKind::Atom(a),
            ..
        }) = self.peek()
        {
            if !a.starts_with(':') || a == ":type" {
                break;
            }
            let key = a[1..].to_string();
            self.next();
            let val = match self.next() {
                Some(STok {
                    kind: STokKind::Str(s),
                    ..
                }) => s,
                Some(STok {
                    kind: STokKind::Atom(s),
                    ..
                }) => s,
                _ => return self.err("expected metadata value after ':key'"),
            };
            meta.insert(key, val);
        }
        Ok(meta)
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut module = HubModule::new();
        let mut pending_comments = Vec::new();

        while let Some(tok) = self.peek() {
            match &tok.kind {
                STokKind::Comment(c) => {
                    pending_comments.push(c.clone());
                    self.next();
                }
                STokKind::LParen => {
                    self.next();
                    let head = self.expect_atom()?;
                    let comments = std::mem::take(&mut pending_comments);
                    match head.as_str() {
                        "struct" => {
                            let s = self.parse_struct(comments)?;
                            module.items.push(Item::Struct(s));
                        }
                        "enum" => {
                            let e = self.parse_enum(comments)?;
                            module.items.push(Item::Enum(e));
                        }
                        "fn" => {
                            let f = self.parse_fn(comments)?;
                            module.items.push(Item::Function(f));
                        }
                        "test" => {
                            let t = self.parse_test(comments)?;
                            module.items.push(Item::Test(t));
                        }
                        other => {
                            return self.err(format!(
                                "expected top-level 'struct', 'enum', 'fn', or 'test', found '{}'",
                                other
                            ));
                        }
                    }
                }
                _ => return self.err("expected '(' at top level"),
            }
        }
        Ok(module)
    }

    fn parse_struct(&mut self, comments: Vec<String>) -> Result<StructDecl, Diagnostic> {
        let name = self.expect_atom()?;
        let meta = self.parse_meta()?;
        let mut fields = Vec::new();
        while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
            self.expect_lparen()?;
            let kw = self.expect_atom()?;
            if kw != "field" {
                return self.err("expected '(field <name> <Type>)' in struct");
            }
            let fname = self.expect_atom()?;
            let fty = self.parse_type()?;
            let fmeta = self.parse_meta()?;
            self.expect_rparen()?;
            fields.push(Field {
                id: 0,
                name: fname,
                ty: fty,
                meta: fmeta,
            });
        }
        self.expect_rparen()?;
        Ok(StructDecl {
            id: 0,
            name,
            fields,
            comments,
            meta,
        })
    }

    fn parse_enum(&mut self, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        let name = self.expect_atom()?;
        let meta = self.parse_meta()?;
        let mut variants = Vec::new();
        while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
            variants.push(self.expect_atom()?);
        }
        self.expect_rparen()?;
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta,
        })
    }

    fn parse_fn(&mut self, comments: Vec<String>) -> Result<FnDecl, Diagnostic> {
        let name = self.expect_atom()?;
        self.expect_lparen()?;
        let mut params = Vec::new();
        while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
            self.expect_lparen()?;
            let kw = self.expect_atom()?;
            if kw != "param" {
                return self.err("expected '(param <name> <Type>)'");
            }
            let pname = self.expect_atom()?;
            let pty = self.parse_type()?;
            let pmeta = self.parse_meta()?;
            self.expect_rparen()?;
            params.push(Param {
                id: 0,
                name: pname,
                ty: pty,
                meta: pmeta,
            });
        }
        self.expect_rparen()?;

        let mut ret_ty = Type::Void;
        if matches!(
            self.peek().map(|t| &t.kind),
            Some(STokKind::Atom(a)) if a == "->"
        ) {
            self.next();
            ret_ty = self.parse_type()?;
        }

        let meta = self.parse_meta()?;
        let mut body = Vec::new();
        while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
            body.push(self.parse_stmt()?);
        }
        self.expect_rparen()?;

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

    fn parse_test(&mut self, comments: Vec<String>) -> Result<TestDecl, Diagnostic> {
        let name = self.expect_atom()?;
        let meta = self.parse_meta()?;
        let mut body = Vec::new();
        while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
            body.push(self.parse_stmt()?);
        }
        self.expect_rparen()?;
        Ok(TestDecl {
            id: 0,
            name,
            body,
            comments,
            meta,
        })
    }

    fn parse_type(&mut self) -> Result<Type, Diagnostic> {
        match self.peek().map(|t| &t.kind) {
            Some(STokKind::LParen) => {
                self.next();
                let kw = self.expect_atom()?;
                if kw != "List" {
                    return self.err(format!("unknown compound type '{}'", kw));
                }
                let inner = self.parse_type()?;
                self.expect_rparen()?;
                Ok(Type::list(inner))
            }
            Some(STokKind::Atom(_)) => {
                let name = self.expect_atom()?;
                Ok(match name.as_str() {
                    "Int" => Type::Int,
                    "Float" => Type::Float,
                    "Bool" => Type::Bool,
                    "Str" => Type::Str,
                    "Void" => Type::Void,
                    other => Type::Named(other.to_string()),
                })
            }
            _ => self.err("expected type"),
        }
    }

    fn parse_pat(&mut self) -> Result<MatchPat, Diagnostic> {
        match self.next() {
            Some(STok {
                kind: STokKind::Str(s),
                ..
            }) => Ok(MatchPat::Str(s)),
            Some(STok {
                kind: STokKind::Atom(a),
                ..
            }) => {
                if a == "_" {
                    return Ok(MatchPat::Wildcard);
                }
                if let Ok(v) = a.parse::<i64>() {
                    return Ok(MatchPat::Int(v));
                }
                if let Some((ename, vname)) = a.split_once("::") {
                    return Ok(MatchPat::EnumVariant {
                        enum_name: ename.to_string(),
                        variant: vname.to_string(),
                    });
                }
                self.err(format!("invalid match pattern '{}'", a))
            }
            _ => self.err("expected match pattern"),
        }
    }

    fn parse_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        if let Some(STok {
            kind: STokKind::Comment(text),
            ..
        }) = self.peek().cloned()
        {
            self.next();
            return Ok(Stmt::Comment { id: 0, text });
        }

        if !matches!(self.peek().map(|t| &t.kind), Some(STokKind::LParen)) {
            let expr = self.parse_expr()?;
            return Ok(Stmt::Expr {
                id: 0,
                expr,
                meta: Metadata::new(),
            });
        }

        let saved_pos = self.pos;
        self.expect_lparen()?;
        let head = match self.peek().map(|t| &t.kind) {
            Some(STokKind::Atom(a)) => a.clone(),
            _ => {
                self.pos = saved_pos;
                let expr = self.parse_expr()?;
                return Ok(Stmt::Expr {
                    id: 0,
                    expr,
                    meta: Metadata::new(),
                });
            }
        };

        match head.as_str() {
            "let" | "let-mut" => {
                self.next();
                let mutable = head == "let-mut";
                let name = self.expect_atom()?;
                let mut ty = None;
                if matches!(
                    self.peek().map(|t| &t.kind),
                    Some(STokKind::Atom(a)) if a == ":type"
                ) {
                    self.next();
                    ty = Some(self.parse_type()?);
                }
                let value = self.parse_expr()?;
                let mut meta = self.parse_meta()?;
                if mutable {
                    meta.insert("explicit_mut".to_string(), "true".to_string());
                }
                self.expect_rparen()?;
                Ok(Stmt::Let {
                    id: 0,
                    name,
                    mutable,
                    ty,
                    value,
                    meta,
                })
            }
            "set!" | "add!" | "sub!" => {
                self.next();
                let op = match head.as_str() {
                    "set!" => AssignOp::Set,
                    "add!" => AssignOp::AddAssign,
                    _ => AssignOp::SubAssign,
                };
                let target = self.parse_assign_target()?;
                let value = self.parse_expr()?;
                self.expect_rparen()?;
                Ok(Stmt::Assign {
                    id: 0,
                    target,
                    op,
                    value,
                    meta: Metadata::new(),
                })
            }
            "if" => {
                self.next();
                let cond = self.parse_expr()?;
                self.expect_lparen()?;
                let then_kw = self.expect_atom()?;
                if then_kw != "then" {
                    return self.err("expected '(then ...)' inside 'if'");
                }
                let mut then_body = Vec::new();
                while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
                    then_body.push(self.parse_stmt()?);
                }
                self.expect_rparen()?;

                let mut else_body = Vec::new();
                if matches!(self.peek().map(|t| &t.kind), Some(STokKind::LParen)) {
                    self.expect_lparen()?;
                    let else_kw = self.expect_atom()?;
                    if else_kw != "else" {
                        return self.err("expected '(else ...)' inside 'if'");
                    }
                    while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
                        else_body.push(self.parse_stmt()?);
                    }
                    self.expect_rparen()?;
                }
                self.expect_rparen()?;
                Ok(Stmt::If {
                    id: 0,
                    cond,
                    then_body,
                    else_body,
                    meta: Metadata::new(),
                })
            }
            "match" => {
                self.next();
                let expr = self.parse_expr()?;
                let mut arms = Vec::new();
                while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
                    self.expect_lparen()?;
                    let kw = self.expect_atom()?;
                    let pat = if kw == "default" {
                        MatchPat::Wildcard
                    } else if kw == "case" {
                        self.parse_pat()?
                    } else {
                        return self.err("expected '(case <pat> ...)' in match");
                    };
                    let mut body = Vec::new();
                    while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
                        body.push(self.parse_stmt()?);
                    }
                    self.expect_rparen()?;
                    arms.push(MatchArm { pat, body });
                }
                self.expect_rparen()?;
                Ok(Stmt::Match {
                    id: 0,
                    expr,
                    arms,
                    meta: Metadata::new(),
                })
            }
            "while" => {
                self.next();
                let cond = self.parse_expr()?;
                let mut body = Vec::new();
                while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
                    body.push(self.parse_stmt()?);
                }
                self.expect_rparen()?;
                Ok(Stmt::While {
                    id: 0,
                    cond,
                    body,
                    meta: Metadata::new(),
                })
            }
            "for-each" => {
                self.next();
                let var = self.expect_atom()?;
                let iter = self.parse_expr()?;
                let mut body = Vec::new();
                while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
                    body.push(self.parse_stmt()?);
                }
                self.expect_rparen()?;
                Ok(Stmt::ForEach {
                    id: 0,
                    var,
                    iter,
                    body,
                    meta: Metadata::new(),
                })
            }
            "for-range" => {
                self.next();
                let var = self.expect_atom()?;
                let start = self.parse_expr()?;
                let end = self.parse_expr()?;
                let mut body = Vec::new();
                while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None) {
                    body.push(self.parse_stmt()?);
                }
                self.expect_rparen()?;
                Ok(Stmt::ForRange {
                    id: 0,
                    var,
                    start,
                    end,
                    body,
                    meta: Metadata::new(),
                })
            }
            "break" => {
                self.next();
                self.expect_rparen()?;
                Ok(Stmt::Break { id: 0 })
            }
            "continue" => {
                self.next();
                self.expect_rparen()?;
                Ok(Stmt::Continue { id: 0 })
            }
            "return" => {
                self.next();
                if matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen)) {
                    self.expect_rparen()?;
                    Ok(Stmt::Return {
                        id: 0,
                        value: None,
                        meta: Metadata::new(),
                    })
                } else {
                    let val = self.parse_expr()?;
                    self.expect_rparen()?;
                    Ok(Stmt::Return {
                        id: 0,
                        value: Some(val),
                        meta: Metadata::new(),
                    })
                }
            }
            "assert" => {
                self.next();
                let cond = self.parse_expr()?;
                self.expect_rparen()?;
                Ok(Stmt::Assert {
                    id: 0,
                    cond,
                    meta: Metadata::new(),
                })
            }
            "assert-eq" => {
                self.next();
                let left = self.parse_expr()?;
                let right = self.parse_expr()?;
                self.expect_rparen()?;
                Ok(Stmt::AssertEq {
                    id: 0,
                    left,
                    right,
                    meta: Metadata::new(),
                })
            }
            _ => {
                self.pos = saved_pos;
                let expr = self.parse_expr()?;
                Ok(Stmt::Expr {
                    id: 0,
                    expr,
                    meta: Metadata::new(),
                })
            }
        }
    }

    fn parse_assign_target(&mut self) -> Result<AssignTarget, Diagnostic> {
        if matches!(self.peek().map(|t| &t.kind), Some(STokKind::LParen)) {
            self.expect_lparen()?;
            let kind = self.expect_atom()?;
            match kind.as_str() {
                "field" => {
                    let base = self.expect_atom()?;
                    let field = self.expect_atom()?;
                    self.expect_rparen()?;
                    Ok(AssignTarget::Field { base, field })
                }
                "index" => {
                    let base = self.expect_atom()?;
                    let index = self.parse_expr()?;
                    self.expect_rparen()?;
                    Ok(AssignTarget::Index { base, index })
                }
                _ => self.err("expected '(field ...)' or '(index ...)' in assignment target"),
            }
        } else {
            Ok(AssignTarget::Var(self.expect_atom()?))
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, Diagnostic> {
        match self.next() {
            Some(STok {
                kind: STokKind::Str(s),
                ..
            }) => Ok(Expr::Str(s)),
            Some(STok {
                kind: STokKind::Atom(a),
                ..
            }) => {
                if a == "true" {
                    return Ok(Expr::Bool(true));
                }
                if a == "false" {
                    return Ok(Expr::Bool(false));
                }
                if let Ok(i) = a.parse::<i64>() {
                    return Ok(Expr::Int(i));
                }
                if let Ok(f) = a.parse::<f64>() {
                    return Ok(Expr::Float(f));
                }
                if let Some((ename, vname)) = a.split_once("::") {
                    return Ok(Expr::EnumVariant {
                        enum_name: ename.to_string(),
                        variant: vname.to_string(),
                    });
                }
                Ok(Expr::Var(a))
            }
            Some(STok {
                kind: STokKind::LParen,
                ..
            }) => {
                let head = self.expect_atom()?;
                let res = match head.as_str() {
                    "list" => {
                        let mut items = Vec::new();
                        while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None)
                        {
                            items.push(self.parse_expr()?);
                        }
                        Expr::List(items)
                    }
                    "make" => {
                        let name = self.expect_atom()?;
                        let mut fields = Vec::new();
                        while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None)
                        {
                            self.expect_lparen()?;
                            let fname = self.expect_atom()?;
                            let fval = self.parse_expr()?;
                            self.expect_rparen()?;
                            fields.push((fname, fval));
                        }
                        Expr::StructInit { name, fields }
                    }
                    "get-field" => {
                        let base = self.parse_expr()?;
                        let field = self.expect_atom()?;
                        Expr::FieldAccess {
                            base: Box::new(base),
                            field,
                        }
                    }
                    "index" => {
                        let base = self.parse_expr()?;
                        let idx = self.parse_expr()?;
                        Expr::Index {
                            base: Box::new(base),
                            index: Box::new(idx),
                        }
                    }
                    "neg" => Expr::Unary {
                        op: UnaryOp::Neg,
                        expr: Box::new(self.parse_expr()?),
                    },
                    "not" => Expr::Unary {
                        op: UnaryOp::Not,
                        expr: Box::new(self.parse_expr()?),
                    },
                    "+" | "-" | "*" | "/" | "//" | "%" | "==" | "!=" | "<" | "<=" | ">" | ">="
                    | "and" | "or" => {
                        let op = match head.as_str() {
                            "+" => BinOp::Add,
                            "-" => BinOp::Sub,
                            "*" => BinOp::Mul,
                            "/" => BinOp::Div,
                            "//" => BinOp::IntDiv,
                            "%" => BinOp::Mod,
                            "==" => BinOp::Eq,
                            "!=" => BinOp::Ne,
                            "<" => BinOp::Lt,
                            "<=" => BinOp::Le,
                            ">" => BinOp::Gt,
                            ">=" => BinOp::Ge,
                            "and" => BinOp::And,
                            _ => BinOp::Or,
                        };
                        let left = self.parse_expr()?;
                        let right = self.parse_expr()?;
                        Expr::Binary {
                            op,
                            left: Box::new(left),
                            right: Box::new(right),
                        }
                    }
                    "call" => {
                        let func = self.expect_atom()?;
                        let mut args = Vec::new();
                        while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None)
                        {
                            args.push(self.parse_expr()?);
                        }
                        Expr::Call { func, args }
                    }
                    "len" => Expr::intrinsic(Intrinsic::Len(self.parse_expr()?)),
                    "min" => {
                        let a = self.parse_expr()?;
                        let b = self.parse_expr()?;
                        Expr::intrinsic(Intrinsic::Min(a, b))
                    }
                    "max" => {
                        let a = self.parse_expr()?;
                        let b = self.parse_expr()?;
                        Expr::intrinsic(Intrinsic::Max(a, b))
                    }
                    "abs" => Expr::intrinsic(Intrinsic::Abs(self.parse_expr()?)),
                    "push!" => {
                        let list = self.parse_expr()?;
                        let value = self.parse_expr()?;
                        Expr::intrinsic(Intrinsic::Push { list, value })
                    }
                    "print" => {
                        let mut args = Vec::new();
                        while !matches!(self.peek().map(|t| &t.kind), Some(STokKind::RParen) | None)
                        {
                            args.push(self.parse_expr()?);
                        }
                        Expr::intrinsic(Intrinsic::Print(args))
                    }
                    "contains" => {
                        let haystack = self.parse_expr()?;
                        let needle = self.parse_expr()?;
                        Expr::intrinsic(Intrinsic::Contains { haystack, needle })
                    }
                    "upper" => Expr::intrinsic(Intrinsic::Upper(self.parse_expr()?)),
                    "lower" => Expr::intrinsic(Intrinsic::Lower(self.parse_expr()?)),
                    "to-str" => Expr::intrinsic(Intrinsic::ToStr(self.parse_expr()?)),
                    other => {
                        return self.err(format!("unknown Star expression form '({})'", other));
                    }
                };
                self.expect_rparen()?;
                Ok(res)
            }
            _ => self.err("expected expression"),
        }
    }
}

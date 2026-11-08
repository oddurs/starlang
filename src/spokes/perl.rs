use std::collections::{HashMap, HashSet};

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl,
    HubModule, Intrinsic, Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl,
    Type, UnaryOp,
};
use crate::lens::{format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;

pub struct PerlLens;

const PERL_PREAMBLE: &str = r##"# StarLang Modern Perl 5.34 + Signatures Runtime Helpers
use v5.34;
use strict;
use warnings;
use feature 'signatures';
no warnings 'experimental::signatures';
use B ();
use List::Util qw(min max);

sub true()  { return (1 == 1); }
sub false() { return (1 == 0); }

sub star_idiv($a, $b) {
    my $q = int($a / $b);
    return $q == 0 ? 0 : $q;
}

sub star_irem($a, $b) {
    my $r = $a - star_idiv($a, $b) * $b;
    return $r == 0 ? 0 : $r;
}

sub star_tostr($v) {
    return "$v" if ref($v);
    my $sv = B::svref_2object(\$v);
    my $f = $sv->FLAGS;
    if (($f & 0x0700) == 0x0700 && ($v eq "1" || $v eq "")) {
        return $v ? "true" : "false";
    }
    if (($f & 0x0300) != 0 && $v == 0) {
        return "0";
    }
    return "$v";
}

sub star_print(@args) {
    my @parts = map { star_tostr($_) } @args;
    print join(" ", @parts), "\n";
}

sub star_eql($a, $b) {
    my $ra = ref($a);
    my $rb = ref($b);
    return false if $ra ne $rb;
    if ($ra eq '') {
        my $fa = B::svref_2object(\$a)->FLAGS;
        my $fb = B::svref_2object(\$b)->FLAGS;
        if ((($fa & 0x0300) != 0) && (($fb & 0x0300) != 0)) {
            return ($a == $b) ? true : false;
        }
        return ($a eq $b) ? true : false;
    }
    if ($ra eq 'ARRAY') {
        return false if scalar(@$a) != scalar(@$b);
        for my $i (0 .. scalar(@$a) - 1) {
            return false if !star_eql($a->[$i], $b->[$i]);
        }
        return true;
    }
    if ($ra eq 'HASH') {
        return false if scalar(keys %$a) != scalar(keys %$b);
        for my $k (keys %$a) {
            return false if !exists($b->{$k}) || !star_eql($a->{$k}, $b->{$k});
        }
        return true;
    }
    return false;
}

sub star_neql($a, $b) {
    return star_eql($a, $b) ? false : true;
}

sub star_assert($cond) {
    die "assert failed\n" if !$cond;
}

sub star_assert_eq($a, $b) {
    die "assert_eq failed\n" if !star_eql($a, $b);
}

sub star_contains($h, $n) {
    if (ref($h) eq 'ARRAY') {
        for my $item (@$h) {
            return true if star_eql($item, $n);
        }
        return false;
    }
    return index($h, $n) >= 0 ? true : false;
}
# @star-end-preamble
"##;

impl LanguageLens for PerlLens {
    fn id(&self) -> SpokeId {
        SpokeId::Perl
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut fmt = PerlFormatter::new(hub);
        fmt.format_module()
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_perl(source)?;
        let mut known_structs: HashMap<String, Vec<String>> = HashMap::new();
        let mut known_enums: HashSet<String> = HashSet::new();
        for item in &prev_hub.items {
            match item {
                Item::Struct(s) => {
                    known_structs.insert(
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
        prescan_perl_types(&tokens, &mut known_structs, &mut known_enums);

        let mut parser = PerlParser {
            tokens,
            pos: 0,
            known_structs,
            known_enums,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Perl))
    }
}

struct PerlFormatter<'a> {
    hub: &'a HubModule,
    struct_names: HashSet<String>,
    fn_ret_types: HashMap<String, Type>,
    struct_fields: HashMap<String, HashMap<String, Type>>,
    enum_names: HashSet<String>,
    env: HashMap<String, Type>,
}

impl<'a> PerlFormatter<'a> {
    fn new(hub: &'a HubModule) -> Self {
        let mut struct_names = HashSet::new();
        let mut fn_ret_types = HashMap::new();
        let mut struct_fields = HashMap::new();
        let mut enum_names = HashSet::new();
        for item in &hub.items {
            match item {
                Item::Struct(s) => {
                    struct_names.insert(s.name.clone());
                    let mut fmap = HashMap::new();
                    for fl in &s.fields {
                        fmap.insert(fl.name.clone(), fl.ty.clone());
                    }
                    struct_fields.insert(s.name.clone(), fmap);
                }
                Item::Function(f) => {
                    fn_ret_types.insert(f.name.clone(), f.ret_ty.clone());
                }
                Item::Enum(e) => {
                    enum_names.insert(e.name.clone());
                }
                Item::Test(_) => {}
            }
        }
        Self {
            hub,
            struct_names,
            fn_ret_types,
            struct_fields,
            enum_names,
            env: HashMap::new(),
        }
    }

    fn format_module(&mut self) -> String {
        let mut out = String::from(PERL_PREAMBLE);
        for item in &self.hub.items {
            out.push('\n');
            match item {
                Item::Enum(e) => self.fmt_enum(e, &mut out),
                Item::Struct(s) => self.fmt_struct(s, &mut out),
                Item::Function(f) => self.fmt_fn(f, &mut out),
                Item::Test(t) => self.fmt_test(t, &mut out),
            }
        }
        if self.hub.has_main() {
            out.push_str("\nmain();\n");
        }
        out
    }

    fn fmt_type(&self, ty: &Type) -> String {
        match ty {
            Type::Int => "Int".to_string(),
            Type::Float => "Float".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Str => "Str".to_string(),
            Type::Void => "Void".to_string(),
            Type::List(inner) => format!("List[{}]", self.fmt_type(inner)),
            Type::Named(name) => name.clone(),
        }
    }

    fn fmt_enum(&self, e: &EnumDecl, out: &mut String) {
        for c in &e.comments {
            out.push_str(&format!("# {}\n", c));
        }
        out.push_str(&format!("# @enum {}\n", e.name));
        out.push_str(&format!("my ${} = {{\n", e.name));
        for (idx, v) in e.variants.iter().enumerate() {
            out.push_str(&format!("    {} => {},\n", v, idx));
        }
        out.push_str("};\n");
    }

    fn fmt_struct(&self, s: &StructDecl, out: &mut String) {
        for c in &s.comments {
            out.push_str(&format!("# {}\n", c));
        }
        out.push_str(&format!("# @class {}\n", s.name));
        for f in &s.fields {
            out.push_str(&format!("# @field {} {}\n", f.name, self.fmt_type(&f.ty)));
        }
        out.push_str(&format!("sub new_{}($o) {{ return $o; }}\n", s.name));
    }

    fn fmt_fn(&mut self, f: &FnDecl, out: &mut String) {
        self.env.clear();
        for c in &f.comments {
            out.push_str(&format!("# {}\n", c));
        }
        for p in &f.params {
            self.env.insert(p.name.clone(), p.ty.clone());
            out.push_str(&format!("# @param ${} {}\n", p.name, self.fmt_type(&p.ty)));
        }
        if f.ret_ty != Type::Void {
            out.push_str(&format!("# @return {}\n", self.fmt_type(&f.ret_ty)));
        }
        let param_sigs: Vec<String> = f.params.iter().map(|p| format!("${}", p.name)).collect();
        out.push_str(&format!("sub {}({}) {{\n", f.name, param_sigs.join(", ")));
        let mut list_hints = HashMap::new();
        self.collect_push_hints(&f.body, &mut list_hints);
        for stmt in &f.body {
            self.fmt_stmt(stmt, 1, &list_hints, out);
        }
        out.push_str("}\n");
    }

    fn fmt_test(&mut self, t: &TestDecl, out: &mut String) {
        self.env.clear();
        for c in &t.comments {
            out.push_str(&format!("# {}\n", c));
        }
        out.push_str(&format!("sub test_{}() {{\n", t.name));
        let mut list_hints = HashMap::new();
        self.collect_push_hints(&t.body, &mut list_hints);
        for stmt in &t.body {
            self.fmt_stmt(stmt, 1, &list_hints, out);
        }
        out.push_str("}\n");
    }

    fn collect_push_hints(&self, stmts: &[Stmt], hints: &mut HashMap<String, Type>) {
        let mut tmp_env = self.env.clone();
        for s in stmts {
            match s {
                Stmt::Let {
                    name, ty, value, ..
                } => {
                    if let Some(t) = ty.clone().or_else(|| {
                        infer_expr_type(
                            value,
                            &tmp_env,
                            &self.fn_ret_types,
                            &self.struct_fields,
                            &self.enum_names,
                        )
                    }) {
                        tmp_env.insert(name.clone(), t);
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
                        if let Some(elem_ty) = infer_expr_type(
                            value,
                            &tmp_env,
                            &self.fn_ret_types,
                            &self.struct_fields,
                            &self.enum_names,
                        ) {
                            hints.insert(v.clone(), Type::List(Box::new(elem_ty)));
                        }
                    }
                }
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    self.collect_push_hints(then_body, hints);
                    self.collect_push_hints(else_body, hints);
                }
                Stmt::Match { arms, .. } => {
                    for a in arms {
                        self.collect_push_hints(&a.body, hints);
                    }
                }
                Stmt::While { body, .. }
                | Stmt::ForEach { body, .. }
                | Stmt::ForRange { body, .. } => {
                    self.collect_push_hints(body, hints);
                }
                _ => {}
            }
        }
    }

    fn expr_type(&self, expr: &Expr) -> Option<Type> {
        infer_expr_type(
            expr,
            &self.env,
            &self.fn_ret_types,
            &self.struct_fields,
            &self.enum_names,
        )
    }

    fn target_type(&self, target: &AssignTarget) -> Option<Type> {
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
        self.expr_type(&target_expr)
    }

    fn is_str_expr(&self, expr: &Expr) -> bool {
        if self.expr_type(expr) == Some(Type::Str) {
            return true;
        }
        match expr {
            Expr::Str(_) => true,
            Expr::Intrinsic(intr) => matches!(
                intr.as_ref(),
                Intrinsic::ToStr(_) | Intrinsic::Upper(_) | Intrinsic::Lower(_)
            ),
            Expr::Binary {
                op: BinOp::Add,
                left,
                right,
            } => self.is_str_expr(left) || self.is_str_expr(right),
            _ => false,
        }
    }

    fn is_deep_eq_type(&self, ty: &Type) -> bool {
        match ty {
            Type::List(_) => true,
            Type::Named(n) => self.struct_names.contains(n),
            _ => false,
        }
    }

    fn fmt_stmt(
        &mut self,
        stmt: &Stmt,
        indent: usize,
        list_hints: &HashMap<String, Type>,
        out: &mut String,
    ) {
        let pad = "    ".repeat(indent);
        match stmt {
            Stmt::Comment { text, .. } => {
                out.push_str(&format!("{}# {}\n", pad, text));
            }
            Stmt::Let {
                name,
                mutable,
                ty,
                value,
                ..
            } => {
                let resolved_ty = ty
                    .clone()
                    .or_else(|| self.expr_type(value))
                    .or_else(|| list_hints.get(name).cloned())
                    .or_else(|| match value {
                        Expr::List(_) => Some(Type::List(Box::new(Type::Int))),
                        _ => None,
                    });
                if let Some(t) = &resolved_ty {
                    self.env.insert(name.clone(), t.clone());
                }
                if let Some(explicit_ty) = ty {
                    out.push_str(&format!("{}# @type {}\n", pad, self.fmt_type(explicit_ty)));
                } else if matches!(value, Expr::List(items) if items.is_empty()) {
                    if let Some(inferred) = list_hints.get(name) {
                        out.push_str(&format!("{}# @type {}\n", pad, self.fmt_type(inferred)));
                    }
                }
                let val_str = self.fmt_expr(value);
                if !mutable {
                    out.push_str(&format!("{}my ${} = {}; # @star-const\n", pad, name, val_str));
                } else {
                    out.push_str(&format!("{}my ${} = {};\n", pad, name, val_str));
                }
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let tgt_str = match target {
                    AssignTarget::Var(v) => format!("${}", v),
                    AssignTarget::Field { base, field } => format!("${}->{{{}}}", base, field),
                    AssignTarget::Index { base, index } => {
                        format!("${}->[{}]", base, self.fmt_expr(index))
                    }
                };
                match op {
                    AssignOp::Set => {
                        out.push_str(&format!("{}{} = {};\n", pad, tgt_str, self.fmt_expr(value)));
                    }
                    AssignOp::AddAssign => {
                        let is_str =
                            self.target_type(target) == Some(Type::Str) || self.is_str_expr(value);
                        let op_str = if is_str { ".=" } else { "+=" };
                        out.push_str(&format!(
                            "{}{} {} {};\n",
                            pad,
                            tgt_str,
                            op_str,
                            self.fmt_expr(value)
                        ));
                    }
                    AssignOp::SubAssign => {
                        out.push_str(&format!(
                            "{}{} -= {};\n",
                            pad,
                            tgt_str,
                            self.fmt_expr(value)
                        ));
                    }
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                out.push_str(&format!("{}if ({}) {{\n", pad, self.fmt_expr(cond)));
                let saved = self.env.clone();
                for s in then_body {
                    self.fmt_stmt(s, indent + 1, list_hints, out);
                }
                self.env = saved;
                self.fmt_else_chain(else_body, indent, list_hints, out);
            }
            Stmt::Match { expr, arms, .. } => {
                out.push_str(&format!("{}if (1) {{ # @star-match\n", pad));
                let inner_pad = "    ".repeat(indent + 1);
                out.push_str(&format!(
                    "{}my $__star_m = {};\n",
                    inner_pad,
                    self.fmt_expr(expr)
                ));
                let is_str = self.is_str_expr(expr)
                    || arms
                        .iter()
                        .any(|a| matches!(a.pat, MatchPat::Str(_)));
                for (idx, arm) in arms.iter().enumerate() {
                    let is_wildcard = matches!(arm.pat, MatchPat::Wildcard);
                    if is_wildcard {
                        if idx == 0 {
                            out.push_str(&format!("{}if (1) {{\n", inner_pad));
                        } else {
                            out.push_str(&format!("{}}} else {{\n", inner_pad));
                        }
                    } else {
                        let cond = self.fmt_match_pat(&arm.pat, is_str);
                        let kw = if idx == 0 { "if" } else { "} elsif" };
                        out.push_str(&format!("{}{} ({}) {{\n", inner_pad, kw, cond));
                    }
                    let saved = self.env.clone();
                    for s in &arm.body {
                        self.fmt_stmt(s, indent + 2, list_hints, out);
                    }
                    self.env = saved;
                }
                if !arms.is_empty() {
                    out.push_str(&format!("{}}}\n", inner_pad));
                }
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::While { cond, body, .. } => {
                out.push_str(&format!("{}while ({}) {{\n", pad, self.fmt_expr(cond)));
                let saved = self.env.clone();
                for s in body {
                    self.fmt_stmt(s, indent + 1, list_hints, out);
                }
                self.env = saved;
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                let start_str = self.fmt_expr(start);
                let hi_str = match end {
                    Expr::Int(n) => format!("{}", n - 1),
                    other => {
                        let e_str = self.fmt_expr(other);
                        if matches!(other, Expr::Binary { .. }) {
                            format!("({}) - 1", e_str)
                        } else {
                            format!("{} - 1", e_str)
                        }
                    }
                };
                out.push_str(&format!(
                    "{}for my ${} ({} .. {}) {{\n",
                    pad, var, start_str, hi_str
                ));
                let saved = self.env.clone();
                self.env.insert(var.clone(), Type::Int);
                for s in body {
                    self.fmt_stmt(s, indent + 1, list_hints, out);
                }
                self.env = saved;
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let iter_str = self.fmt_expr(iter);
                out.push_str(&format!("{}for my ${} (@{{{}}}) {{\n", pad, var, iter_str));
                let saved = self.env.clone();
                if let Some(Type::List(elem)) = self.expr_type(iter) {
                    self.env.insert(var.clone(), *elem);
                }
                for s in body {
                    self.fmt_stmt(s, indent + 1, list_hints, out);
                }
                self.env = saved;
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    out.push_str(&format!("{}return {};\n", pad, self.fmt_expr(v)));
                } else {
                    out.push_str(&format!("{}return;\n", pad));
                }
            }
            Stmt::Break { .. } => {
                out.push_str(&format!("{}last;\n", pad));
            }
            Stmt::Continue { .. } => {
                out.push_str(&format!("{}next;\n", pad));
            }
            Stmt::Assert { cond, .. } => {
                out.push_str(&format!("{}star_assert({});\n", pad, self.fmt_expr(cond)));
            }
            Stmt::AssertEq { left, right, .. } => {
                out.push_str(&format!(
                    "{}star_assert_eq({}, {});\n",
                    pad,
                    self.fmt_expr(left),
                    self.fmt_expr(right)
                ));
            }
            Stmt::Expr { expr, .. } => {
                out.push_str(&format!("{}{};\n", pad, self.fmt_expr(expr)));
            }
        }
    }

    fn fmt_else_chain(
        &mut self,
        else_body: &[Stmt],
        indent: usize,
        list_hints: &HashMap<String, Type>,
        out: &mut String,
    ) {
        let pad = "    ".repeat(indent);
        if else_body.is_empty() {
            out.push_str(&format!("{}}}\n", pad));
            return;
        }
        if else_body.len() == 1 {
            if let Stmt::If {
                cond,
                then_body,
                else_body: next_else,
                ..
            } = &else_body[0]
            {
                out.push_str(&format!("{}}} elsif ({}) {{\n", pad, self.fmt_expr(cond)));
                let saved = self.env.clone();
                for s in then_body {
                    self.fmt_stmt(s, indent + 1, list_hints, out);
                }
                self.env = saved;
                self.fmt_else_chain(next_else, indent, list_hints, out);
                return;
            }
        }
        out.push_str(&format!("{}}} else {{\n", pad));
        let saved = self.env.clone();
        for s in else_body {
            self.fmt_stmt(s, indent + 1, list_hints, out);
        }
        self.env = saved;
        out.push_str(&format!("{}}}\n", pad));
    }

    fn fmt_match_pat(&self, pat: &MatchPat, is_str: bool) -> String {
        match pat {
            MatchPat::Int(v) => format!("$__star_m == {}", v),
            MatchPat::Str(s) => format!("$__star_m eq \"{}\"", escape_perl_str(s)),
            MatchPat::EnumVariant { enum_name, variant } => {
                if is_str {
                    format!("$__star_m eq ${}->{{{}}}", enum_name, variant)
                } else {
                    format!("$__star_m == ${}->{{{}}}", enum_name, variant)
                }
            }
            MatchPat::Wildcard => "1".to_string(),
        }
    }

    fn fmt_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => format!("{}", v),
            Expr::Float(v) => format_float(*v),
            Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Expr::Str(s) => format!("\"{}\"", escape_perl_str(s)),
            Expr::Var(name) => format!("${}", name),
            Expr::List(items) => {
                let parts: Vec<String> = items.iter().map(|e| self.fmt_expr(e)).collect();
                format!("[{}]", parts.join(", "))
            }
            Expr::StructInit { name, fields } => {
                let f_parts: Vec<String> = fields
                    .iter()
                    .map(|(k, v)| format!("{} => {}", k, self.fmt_expr(v)))
                    .collect();
                format!("new_{}({{ {} }})", name, f_parts.join(", "))
            }
            Expr::EnumVariant { enum_name, variant } => {
                format!("${}->{{{}}}", enum_name, variant)
            }
            Expr::FieldAccess { base, field } => {
                let b_str = self.fmt_postfix_base(base);
                format!("{}->{{{}}}", b_str, field)
            }
            Expr::Index { base, index } => {
                let b_str = self.fmt_postfix_base(base);
                format!("{}->[{}]", b_str, self.fmt_expr(index))
            }
            Expr::Unary { op, expr: inner } => {
                let inner_str = self.fmt_expr(inner);
                let wrap = matches!(inner.as_ref(), Expr::Binary { .. } | Expr::Unary { .. })
                    || (*op == UnaryOp::Neg && inner_str.starts_with('-'));
                match op {
                    UnaryOp::Neg => {
                        if wrap {
                            format!("-({})", inner_str)
                        } else {
                            format!("-{}", inner_str)
                        }
                    }
                    UnaryOp::Not => {
                        if wrap {
                            format!("!({})", inner_str)
                        } else {
                            format!("!{}", inner_str)
                        }
                    }
                }
            }
            Expr::Binary { op, left, right } => {
                if *op == BinOp::IntDiv {
                    return format!("star_idiv({}, {})", self.fmt_expr(left), self.fmt_expr(right));
                }
                if *op == BinOp::Mod {
                    return format!("star_irem({}, {})", self.fmt_expr(left), self.fmt_expr(right));
                }
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    let lty = self.expr_type(left);
                    let rty = self.expr_type(right);
                    let deep = lty.as_ref().is_some_and(|t| self.is_deep_eq_type(t))
                        || rty.as_ref().is_some_and(|t| self.is_deep_eq_type(t))
                        || matches!(
                            left.as_ref(),
                            Expr::List(_) | Expr::StructInit { .. }
                        )
                        || matches!(
                            right.as_ref(),
                            Expr::List(_) | Expr::StructInit { .. }
                        );
                    if deep {
                        let fn_name = if *op == BinOp::Eq {
                            "star_eql"
                        } else {
                            "star_neql"
                        };
                        return format!(
                            "{}({}, {})",
                            fn_name,
                            self.fmt_expr(left),
                            self.fmt_expr(right)
                        );
                    }
                }

                let lhs_raw = self.fmt_expr(left);
                let rhs_raw = self.fmt_expr(right);
                let lhs = if needs_parens(left, *op, false) {
                    format!("({})", lhs_raw)
                } else {
                    lhs_raw
                };
                let rhs = if needs_parens(right, *op, true)
                    || (*op == BinOp::Sub
                        && matches!(
                            right.as_ref(),
                            Expr::Unary {
                                op: UnaryOp::Neg,
                                ..
                            }
                        ))
                {
                    format!("({})", rhs_raw)
                } else {
                    rhs_raw
                };

                let is_str = self.is_str_expr(left) || self.is_str_expr(right);
                let op_str = match op {
                    BinOp::Add => {
                        if is_str {
                            "."
                        } else {
                            "+"
                        }
                    }
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => "/",
                    BinOp::IntDiv | BinOp::Mod => unreachable!(),
                    BinOp::Eq => {
                        if is_str {
                            "eq"
                        } else {
                            "=="
                        }
                    }
                    BinOp::Ne => {
                        if is_str {
                            "ne"
                        } else {
                            "!="
                        }
                    }
                    BinOp::Lt => {
                        if is_str {
                            "lt"
                        } else {
                            "<"
                        }
                    }
                    BinOp::Le => {
                        if is_str {
                            "le"
                        } else {
                            "<="
                        }
                    }
                    BinOp::Gt => {
                        if is_str {
                            "gt"
                        } else {
                            ">"
                        }
                    }
                    BinOp::Ge => {
                        if is_str {
                            "ge"
                        } else {
                            ">="
                        }
                    }
                    BinOp::And => "&&",
                    BinOp::Or => "||",
                };

                format!("{} {} {}", lhs, op_str, rhs)
            }
            Expr::Call { func, args } => {
                let a_parts: Vec<String> = args.iter().map(|a| self.fmt_expr(a)).collect();
                format!("{}({})", func, a_parts.join(", "))
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(x) => {
                    if self.is_str_expr(x) {
                        format!("length({})", self.fmt_expr(x))
                    } else {
                        format!("scalar(@{{{}}})", self.fmt_expr(x))
                    }
                }
                Intrinsic::Push { list, value } => {
                    format!(
                        "push(@{{{}}}, {})",
                        self.fmt_expr(list),
                        self.fmt_expr(value)
                    )
                }
                Intrinsic::Min(a, b) => {
                    format!("min({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Max(a, b) => {
                    format!("max({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Abs(a) => format!("abs({})", self.fmt_expr(a)),
                Intrinsic::Upper(a) => format!("uc({})", self.fmt_expr(a)),
                Intrinsic::Lower(a) => format!("lc({})", self.fmt_expr(a)),
                Intrinsic::ToStr(a) => format!("star_tostr({})", self.fmt_expr(a)),
                Intrinsic::Contains { haystack, needle } => {
                    format!(
                        "star_contains({}, {})",
                        self.fmt_expr(haystack),
                        self.fmt_expr(needle)
                    )
                }
                Intrinsic::Print(args) => {
                    let a_parts: Vec<String> = args.iter().map(|a| self.fmt_expr(a)).collect();
                    format!("star_print({})", a_parts.join(", "))
                }
            },
        }
    }

    fn fmt_postfix_base(&self, base: &Expr) -> String {
        let s = self.fmt_expr(base);
        if matches!(
            base,
            Expr::Var(_)
                | Expr::FieldAccess { .. }
                | Expr::Index { .. }
                | Expr::Call { .. }
                | Expr::List(_)
        ) {
            s
        } else {
            format!("({})", s)
        }
    }
}

fn escape_perl_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '$' => out.push_str("\\$"),
            '@' => out.push_str("\\@"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            other => out.push(other),
        }
    }
    out
}

fn unescape_perl_str(raw: &str) -> String {
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
                Some('$') => out.push('$'),
                Some('@') => out.push('@'),
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

#[derive(Debug, Clone, PartialEq)]
enum PTokKind {
    Ident(String),
    ScalarVar(String),
    ArrayVar(String),
    Int(i64),
    Float(f64),
    Str(String),
    Comment(String),
    DocType(String),
    Directive(String),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semi,
    Dot,
    DotDot,
    Arrow,
    FatComma,
    At,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Bang,
    Eq,
    PlusEq,
    MinusEq,
    DotEq,
    EqEq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    AndAnd,
    OrOr,
}

#[derive(Debug, Clone)]
struct PTok {
    kind: PTokKind,
    line: usize,
    col: usize,
}

fn lex_perl(source: &str) -> Result<Vec<PTok>, Diagnostic> {
    let body = if let Some(idx) = source.find("# @star-end-preamble") {
        let after = &source[idx + "# @star-end-preamble".len()..];
        after.strip_prefix('\n').unwrap_or(after)
    } else {
        source
    };

    let chars: Vec<char> = body.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut line = 1usize;
    let mut col = 1usize;
    let mut tokens = Vec::new();

    while i < n {
        let c = chars[i];
        if c == '\n' {
            line += 1;
            col = 1;
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            col += 1;
            i += 1;
            continue;
        }

        // Comments & directives
        if c == '#' {
            let start_line = line;
            let start_col = col;
            i += 1;
            col += 1;
            let start = i;
            while i < n && chars[i] != '\n' {
                i += 1;
                col += 1;
            }
            let text: String = chars[start..i].iter().collect();
            let trimmed = text.trim();
            if let Some(dir) = trimmed.strip_prefix("@star-") {
                tokens.push(PTok {
                    kind: PTokKind::Directive(dir.trim().to_string()),
                    line: start_line,
                    col: start_col,
                });
            } else if let Some(doc) = trimmed.strip_prefix('@') {
                tokens.push(PTok {
                    kind: PTokKind::DocType(doc.trim().to_string()),
                    line: start_line,
                    col: start_col,
                });
            } else if !trimmed.starts_with("StarLang ") {
                tokens.push(PTok {
                    kind: PTokKind::Comment(trimmed.to_string()),
                    line: start_line,
                    col: start_col,
                });
            }
            continue;
        }

        let start_line = line;
        let start_col = col;

        // Strings
        if c == '"' || c == '\'' {
            let quote = c;
            i += 1;
            col += 1;
            let mut raw = String::new();
            while i < n && chars[i] != quote {
                if chars[i] == '\\' && i + 1 < n {
                    raw.push(chars[i]);
                    raw.push(chars[i + 1]);
                    i += 2;
                    col += 2;
                } else {
                    if chars[i] == '\n' {
                        line += 1;
                        col = 1;
                    } else {
                        col += 1;
                    }
                    raw.push(chars[i]);
                    i += 1;
                }
            }
            if i >= n {
                return Err(Diagnostic::new(
                    "perl",
                    "unterminated string literal",
                    start_line,
                    start_col,
                ));
            }
            i += 1;
            col += 1;
            tokens.push(PTok {
                kind: PTokKind::Str(unescape_perl_str(&raw)),
                line: start_line,
                col: start_col,
            });
            continue;
        }

        // Scalar variable `$ident`
        if c == '$' {
            i += 1;
            col += 1;
            let start = i;
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            if i == start {
                return Err(Diagnostic::new(
                    "perl",
                    "expected identifier after '$'",
                    start_line,
                    start_col,
                ));
            }
            let ident: String = chars[start..i].iter().collect();
            tokens.push(PTok {
                kind: PTokKind::ScalarVar(ident),
                line: start_line,
                col: start_col,
            });
            continue;
        }

        // Array dereference `@{$expr}` or `@$ident` or `@ident`
        if c == '@' {
            i += 1;
            col += 1;
            if i < n && (chars[i].is_ascii_alphabetic() || chars[i] == '_') {
                let start = i;
                while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                    i += 1;
                    col += 1;
                }
                let ident: String = chars[start..i].iter().collect();
                tokens.push(PTok {
                    kind: PTokKind::ArrayVar(ident),
                    line: start_line,
                    col: start_col,
                });
            } else {
                tokens.push(PTok {
                    kind: PTokKind::At,
                    line: start_line,
                    col: start_col,
                });
            }
            continue;
        }

        // Numbers
        if c.is_ascii_digit() {
            let start = i;
            let mut is_float = false;
            while i < n && chars[i].is_ascii_digit() {
                i += 1;
                col += 1;
            }
            if i + 1 < n && chars[i] == '.' && chars[i + 1].is_ascii_digit() {
                is_float = true;
                i += 1;
                col += 1;
                while i < n && chars[i].is_ascii_digit() {
                    i += 1;
                    col += 1;
                }
            }
            let text: String = chars[start..i].iter().collect();
            if is_float {
                let v = text.parse::<f64>().map_err(|_| {
                    Diagnostic::new("perl", "invalid float literal", start_line, start_col)
                })?;
                tokens.push(PTok {
                    kind: PTokKind::Float(v),
                    line: start_line,
                    col: start_col,
                });
            } else {
                let v = text.parse::<i64>().map_err(|_| {
                    Diagnostic::new("perl", "invalid integer literal", start_line, start_col)
                })?;
                tokens.push(PTok {
                    kind: PTokKind::Int(v),
                    line: start_line,
                    col: start_col,
                });
            }
            continue;
        }

        // Identifiers & keywords
        if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            let ident: String = chars[start..i].iter().collect();
            tokens.push(PTok {
                kind: PTokKind::Ident(ident),
                line: start_line,
                col: start_col,
            });
            continue;
        }

        // Multi-char operators
        let next_ch = if i + 1 < n { Some(chars[i + 1]) } else { None };
        let two = match (c, next_ch) {
            ('-', Some('>')) => Some(PTokKind::Arrow),
            ('=', Some('>')) => Some(PTokKind::FatComma),
            ('.', Some('.')) => Some(PTokKind::DotDot),
            ('+', Some('=')) => Some(PTokKind::PlusEq),
            ('-', Some('=')) => Some(PTokKind::MinusEq),
            ('.', Some('=')) => Some(PTokKind::DotEq),
            ('=', Some('=')) => Some(PTokKind::EqEq),
            ('!', Some('=')) => Some(PTokKind::NotEq),
            ('<', Some('=')) => Some(PTokKind::Le),
            ('>', Some('=')) => Some(PTokKind::Ge),
            ('&', Some('&')) => Some(PTokKind::AndAnd),
            ('|', Some('|')) => Some(PTokKind::OrOr),
            _ => None,
        };
        if let Some(kind) = two {
            tokens.push(PTok {
                kind,
                line: start_line,
                col: start_col,
            });
            i += 2;
            col += 2;
            continue;
        }

        let one = match c {
            '(' => PTokKind::LParen,
            ')' => PTokKind::RParen,
            '[' => PTokKind::LBracket,
            ']' => PTokKind::RBracket,
            '{' => PTokKind::LBrace,
            '}' => PTokKind::RBrace,
            ',' => PTokKind::Comma,
            ';' => PTokKind::Semi,
            '.' => PTokKind::Dot,
            '+' => PTokKind::Plus,
            '-' => PTokKind::Minus,
            '*' => PTokKind::Star,
            '/' => PTokKind::Slash,
            '%' => PTokKind::Percent,
            '!' => PTokKind::Bang,
            '=' => PTokKind::Eq,
            '<' => PTokKind::Lt,
            '>' => PTokKind::Gt,
            other => {
                return Err(Diagnostic::new(
                    "perl",
                    format!("unexpected character '{}' in Perl source", other),
                    start_line,
                    start_col,
                ));
            }
        };
        tokens.push(PTok {
            kind: one,
            line: start_line,
            col: start_col,
        });
        i += 1;
        col += 1;
    }

    Ok(tokens)
}

fn parse_perl_type_str(raw: &str) -> Result<Type, String> {
    let s = raw.trim();
    if let Some(inner) = s.strip_prefix("List[").and_then(|r| r.strip_suffix(']')) {
        let elem = parse_perl_type_str(inner)?;
        return Ok(Type::List(Box::new(elem)));
    }
    if let Some(inner) = s.strip_suffix("[]") {
        let elem = parse_perl_type_str(inner)?;
        return Ok(Type::List(Box::new(elem)));
    }
    match s {
        "Int" | "integer" | "int" | "i64" => Ok(Type::Int),
        "Float" | "number" | "float" | "f64" => Ok(Type::Float),
        "Bool" | "boolean" | "bool" => Ok(Type::Bool),
        "Str" | "string" | "str" => Ok(Type::Str),
        "Void" | "nil" | "void" => Ok(Type::Void),
        other
            if !other.is_empty()
                && other
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_') =>
        {
            Ok(Type::Named(other.to_string()))
        }
        other => Err(format!("unknown Perl type annotation '{}'", other)),
    }
}

fn prescan_perl_types(
    tokens: &[PTok],
    known_structs: &mut HashMap<String, Vec<String>>,
    known_enums: &mut HashSet<String>,
) {
    let mut cur_class: Option<String> = None;
    for tok in tokens {
        if let PTokKind::DocType(doc) = &tok.kind {
            if let Some(rest) = doc.strip_prefix("enum ") {
                let name = rest.split_whitespace().next().unwrap_or("").to_string();
                if !name.is_empty() {
                    known_enums.insert(name);
                }
                cur_class = None;
            } else if let Some(rest) = doc.strip_prefix("class ") {
                let name = rest.split_whitespace().next().unwrap_or("").to_string();
                if !name.is_empty() {
                    known_structs.entry(name.clone()).or_default();
                    cur_class = Some(name);
                }
            } else if let Some(rest) = doc.strip_prefix("field ") {
                if let Some(cls) = &cur_class {
                    if let Some(fname) = rest.split_whitespace().next() {
                        let entry = known_structs.entry(cls.clone()).or_default();
                        if !entry.iter().any(|x| x == fname) {
                            entry.push(fname.to_string());
                        }
                    }
                }
            } else {
                cur_class = None;
            }
        }
    }
}

struct PerlParser {
    tokens: Vec<PTok>,
    pos: usize,
    known_structs: HashMap<String, Vec<String>>,
    known_enums: HashSet<String>,
}

impl PerlParser {
    fn peek(&self) -> Option<&PTok> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&PTokKind> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn peek_kind_at(&self, offset: usize) -> Option<&PTokKind> {
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<PTok> {
        if self.pos < self.tokens.len() {
            let t = self.tokens[self.pos].clone();
            self.pos += 1;
            Some(t)
        } else {
            None
        }
    }

    fn cur_loc(&self) -> (usize, usize) {
        if let Some(t) = self.peek() {
            (t.line, t.col)
        } else if let Some(last) = self.tokens.last() {
            (last.line, last.col)
        } else {
            (1, 1)
        }
    }

    fn err<T>(&self, msg: impl Into<String>) -> Result<T, Diagnostic> {
        let (l, c) = self.cur_loc();
        Err(Diagnostic::new("perl", msg.into(), l, c))
    }

    fn is_kw(&self, kw: &str) -> bool {
        matches!(self.peek_kind(), Some(PTokKind::Ident(s)) if s == kw)
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.is_kw(kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect_kw(&mut self, kw: &str) -> Result<(), Diagnostic> {
        if self.eat_kw(kw) {
            Ok(())
        } else {
            self.err(format!("expected keyword '{}'", kw))
        }
    }

    fn eat(&mut self, kind: &PTokKind) -> bool {
        if self.peek_kind() == Some(kind) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: &PTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(kind) {
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

    fn expect_scalar_var(&mut self) -> Result<String, Diagnostic> {
        match self.next() {
            Some(PTok {
                kind: PTokKind::ScalarVar(s),
                ..
            }) => Ok(s),
            _ => self.err("expected '$variable'"),
        }
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut items = Vec::new();
        let mut pending_comments: Vec<String> = Vec::new();
        let mut pending_docs: Vec<String> = Vec::new();

        while self.pos < self.tokens.len() {
            match self.peek_kind() {
                Some(PTokKind::Semi) => {
                    self.next();
                }
                Some(PTokKind::Comment(_)) => {
                    if let Some(PTok {
                        kind: PTokKind::Comment(c),
                        ..
                    }) = self.next()
                    {
                        pending_comments.push(c);
                    }
                }
                Some(PTokKind::DocType(_)) => {
                    if let Some(PTok {
                        kind: PTokKind::DocType(d),
                        ..
                    }) = self.next()
                    {
                        pending_docs.push(d);
                    }
                }
                Some(PTokKind::Directive(_)) => {
                    self.next();
                }
                Some(PTokKind::Ident(w)) if w == "use" || w == "no" => {
                    while self.pos < self.tokens.len() && !self.eat(&PTokKind::Semi) {
                        self.next();
                    }
                }
                Some(PTokKind::Ident(w))
                    if w == "main" && self.peek_kind_at(1) == Some(&PTokKind::LParen) =>
                {
                    self.next();
                    self.next();
                    let _ = self.eat(&PTokKind::RParen);
                    let _ = self.eat(&PTokKind::Semi);
                }
                Some(PTokKind::Ident(w)) if w == "my" => {
                    // Enum table: `my $EnumName = { Variant => 0, ... };`
                    self.next();
                    let name = self.expect_scalar_var()?;
                    self.expect(&PTokKind::Eq, "'='")?;
                    self.expect(&PTokKind::LBrace, "'{'")?;
                    let mut variants = Vec::new();
                    while !self.eat(&PTokKind::RBrace) {
                        let vname = self.expect_ident()?;
                        self.expect(&PTokKind::FatComma, "'=>'")?;
                        let _ = self.parse_expr()?;
                        let _ = self.eat(&PTokKind::Comma);
                        variants.push(vname);
                    }
                    let _ = self.eat(&PTokKind::Semi);
                    self.known_enums.insert(name.clone());
                    items.push(Item::Enum(EnumDecl {
                        id: 0,
                        name,
                        variants,
                        comments: std::mem::take(&mut pending_comments),
                        meta: Metadata::new(),
                    }));
                    pending_docs.clear();
                }
                Some(PTokKind::Ident(w)) if w == "sub" => {
                    self.next();
                    let sub_name = self.expect_ident()?;
                    if let Some(struct_name) = sub_name.strip_prefix("new_") {
                        if pending_docs.iter().any(|d| d.starts_with("class "))
                            || self.known_structs.contains_key(struct_name)
                        {
                            // Skip `($o) { return $o; }`
                            if self.eat(&PTokKind::LParen) {
                                while !self.eat(&PTokKind::RParen) && self.pos < self.tokens.len() {
                                    self.next();
                                }
                            }
                            self.skip_balanced_braces()?;
                            let mut fields = Vec::new();
                            for d in &pending_docs {
                                if let Some(rest) = d.strip_prefix("field ") {
                                    let mut parts = rest.splitn(2, char::is_whitespace);
                                    let fname = parts.next().unwrap_or("").trim().to_string();
                                    let fty_raw = parts.next().unwrap_or("Int").trim();
                                    let fty = parse_perl_type_str(fty_raw)
                                        .map_err(|e| self.err::<()>(e).unwrap_err())?;
                                    fields.push(Field {
                                        id: 0,
                                        name: fname,
                                        ty: fty,
                                        meta: Metadata::new(),
                                    });
                                }
                            }
                            self.known_structs.insert(
                                struct_name.to_string(),
                                fields.iter().map(|f| f.name.clone()).collect(),
                            );
                            items.push(Item::Struct(StructDecl {
                                id: 0,
                                name: struct_name.to_string(),
                                fields,
                                comments: std::mem::take(&mut pending_comments),
                                meta: Metadata::new(),
                            }));
                            pending_docs.clear();
                            continue;
                        }
                    }

                    let item = self.parse_sub_after_name(
                        sub_name,
                        std::mem::take(&mut pending_comments),
                        std::mem::take(&mut pending_docs),
                    )?;
                    items.push(item);
                }
                _ => {
                    return self.err("unexpected top-level token in Perl module");
                }
            }
        }

        Ok(HubModule { items, next_id: 1 })
    }

    fn skip_balanced_braces(&mut self) -> Result<(), Diagnostic> {
        self.expect(&PTokKind::LBrace, "'{'")?;
        let mut depth = 1usize;
        while self.pos < self.tokens.len() && depth > 0 {
            match self.peek_kind() {
                Some(PTokKind::LBrace) => {
                    depth += 1;
                    self.next();
                }
                Some(PTokKind::RBrace) => {
                    depth -= 1;
                    self.next();
                }
                _ => {
                    self.next();
                }
            }
        }
        Ok(())
    }

    fn parse_sub_after_name(
        &mut self,
        name: String,
        comments: Vec<String>,
        docs: Vec<String>,
    ) -> Result<Item, Diagnostic> {
        let mut doc_params: HashMap<String, Type> = HashMap::new();
        let mut ret_ty = Type::Void;
        for d in &docs {
            if let Some(rest) = d.strip_prefix("param ") {
                let mut parts = rest.splitn(2, char::is_whitespace);
                let raw_pname = parts.next().unwrap_or("").trim();
                let pname = raw_pname.strip_prefix('$').unwrap_or(raw_pname).to_string();
                let pty_str = parts.next().unwrap_or("Int").trim();
                if let Ok(t) = parse_perl_type_str(pty_str) {
                    doc_params.insert(pname, t);
                }
            } else if let Some(rest) = d.strip_prefix("return ") {
                if let Ok(t) = parse_perl_type_str(rest.trim()) {
                    ret_ty = t;
                }
            }
        }

        self.expect(&PTokKind::LParen, "'('")?;
        let mut params = Vec::new();
        while !self.eat(&PTokKind::RParen) {
            let pname = self.expect_scalar_var()?;
            let ty = doc_params.remove(&pname).unwrap_or(Type::Int);
            params.push(Param {
                id: 0,
                name: pname,
                ty,
                meta: Metadata::new(),
            });
            if !self.eat(&PTokKind::Comma) {
                self.expect(&PTokKind::RParen, "')'")?;
                break;
            }
        }

        self.expect(&PTokKind::LBrace, "'{'")?;
        let body = self.parse_block_until_rbrace()?;

        if let Some(test_name) = name.strip_prefix("test_") {
            if params.is_empty() {
                return Ok(Item::Test(TestDecl {
                    id: 0,
                    name: test_name.to_string(),
                    body,
                    comments,
                    meta: Metadata::new(),
                }));
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

    fn parse_block_until_rbrace(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        let mut stmts = Vec::new();
        let mut pending_type: Option<Type> = None;

        while self.pos < self.tokens.len() {
            if self.eat(&PTokKind::RBrace) {
                return Ok(stmts);
            }
            if self.eat(&PTokKind::Semi) {
                continue;
            }
            match self.peek_kind() {
                Some(PTokKind::Comment(_)) => {
                    if let Some(PTok {
                        kind: PTokKind::Comment(text),
                        ..
                    }) = self.next()
                    {
                        stmts.push(Stmt::Comment { id: 0, text });
                    }
                }
                Some(PTokKind::DocType(_)) => {
                    if let Some(PTok {
                        kind: PTokKind::DocType(d),
                        ..
                    }) = self.next()
                    {
                        if let Some(rest) = d.strip_prefix("type ") {
                            if let Ok(t) = parse_perl_type_str(rest.trim()) {
                                pending_type = Some(t);
                            }
                        }
                    }
                }
                Some(PTokKind::Directive(_)) => {
                    self.next();
                }
                _ => {
                    let s = self.parse_stmt(pending_type.take())?;
                    stmts.push(s);
                }
            }
        }

        self.err("expected '}' to close Perl block")
    }

    fn parse_stmt(&mut self, pending_type: Option<Type>) -> Result<Stmt, Diagnostic> {
        if self.eat_kw("my") {
            let name = self.expect_scalar_var()?;
            self.expect(&PTokKind::Eq, "'=' after lexical variable")?;
            let value = self.parse_expr()?;
            let _ = self.eat(&PTokKind::Semi);
            let mutable = if matches!(self.peek_kind(), Some(PTokKind::Directive(d)) if d == "const")
            {
                self.next();
                false
            } else {
                true
            };
            return Ok(Stmt::Let {
                id: 0,
                name,
                mutable,
                ty: pending_type,
                value,
                meta: Metadata::new(),
            });
        }

        if self.eat_kw("if") {
            return self.parse_if_or_match_stmt();
        }

        if self.eat_kw("while") {
            self.expect(&PTokKind::LParen, "'(' after while")?;
            let cond = self.parse_expr()?;
            self.expect(&PTokKind::RParen, "')' after while condition")?;
            self.expect(&PTokKind::LBrace, "'{'")?;
            let body = self.parse_block_until_rbrace()?;
            return Ok(Stmt::While {
                id: 0,
                cond,
                body,
                meta: Metadata::new(),
            });
        }

        if self.eat_kw("for") {
            let _ = self.eat_kw("my");
            let var = self.expect_scalar_var()?;
            self.expect(&PTokKind::LParen, "'(' in Perl for loop")?;
            if self.eat(&PTokKind::At) {
                let iter = if self.eat(&PTokKind::LBrace) {
                    let e = self.parse_expr()?;
                    self.expect(&PTokKind::RBrace, "'}' after @{...}")?;
                    e
                } else {
                    let v = self.expect_scalar_var()?;
                    Expr::Var(v)
                };
                self.expect(&PTokKind::RParen, "')'")?;
                self.expect(&PTokKind::LBrace, "'{'")?;
                let body = self.parse_block_until_rbrace()?;
                return Ok(Stmt::ForEach {
                    id: 0,
                    var,
                    iter,
                    body,
                    meta: Metadata::new(),
                });
            }
            if let Some(PTokKind::ArrayVar(_)) = self.peek_kind() {
                if let Some(PTok {
                    kind: PTokKind::ArrayVar(v),
                    ..
                }) = self.next()
                {
                    self.expect(&PTokKind::RParen, "')'")?;
                    self.expect(&PTokKind::LBrace, "'{'")?;
                    let body = self.parse_block_until_rbrace()?;
                    return Ok(Stmt::ForEach {
                        id: 0,
                        var,
                        iter: Expr::Var(v),
                        body,
                        meta: Metadata::new(),
                    });
                }
            }

            let start = self.parse_expr()?;
            self.expect(&PTokKind::DotDot, "'..' in range loop")?;
            let raw_hi = self.parse_expr()?;
            let end = unlift_perl_range_hi(raw_hi);
            self.expect(&PTokKind::RParen, "')'")?;
            self.expect(&PTokKind::LBrace, "'{'")?;
            let body = self.parse_block_until_rbrace()?;
            return Ok(Stmt::ForRange {
                id: 0,
                var,
                start,
                end,
                body,
                meta: Metadata::new(),
            });
        }

        if self.eat_kw("return") {
            if self.eat(&PTokKind::Semi) || self.peek_kind() == Some(&PTokKind::RBrace) {
                return Ok(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                });
            }
            let val = self.parse_expr()?;
            let _ = self.eat(&PTokKind::Semi);
            return Ok(Stmt::Return {
                id: 0,
                value: Some(val),
                meta: Metadata::new(),
            });
        }

        if self.eat_kw("last") {
            let _ = self.eat(&PTokKind::Semi);
            return Ok(Stmt::Break { id: 0 });
        }

        if self.eat_kw("next") {
            let _ = self.eat(&PTokKind::Semi);
            return Ok(Stmt::Continue { id: 0 });
        }

        if self.is_kw("star_assert") && self.peek_kind_at(1) == Some(&PTokKind::LParen) {
            self.next();
            self.next();
            let cond = self.parse_expr()?;
            self.expect(&PTokKind::RParen, "')'")?;
            let _ = self.eat(&PTokKind::Semi);
            return Ok(Stmt::Assert {
                id: 0,
                cond,
                meta: Metadata::new(),
            });
        }

        if self.is_kw("star_assert_eq") && self.peek_kind_at(1) == Some(&PTokKind::LParen) {
            self.next();
            self.next();
            let left = self.parse_expr()?;
            self.expect(&PTokKind::Comma, "','")?;
            let right = self.parse_expr()?;
            self.expect(&PTokKind::RParen, "')'")?;
            let _ = self.eat(&PTokKind::Semi);
            return Ok(Stmt::AssertEq {
                id: 0,
                left,
                right,
                meta: Metadata::new(),
            });
        }

        // Assignment or expression statement
        let lhs = self.parse_expr()?;
        if let Some(op) = match self.peek_kind() {
            Some(PTokKind::Eq) => Some(AssignOp::Set),
            Some(PTokKind::PlusEq) | Some(PTokKind::DotEq) => Some(AssignOp::AddAssign),
            Some(PTokKind::MinusEq) => Some(AssignOp::SubAssign),
            _ => None,
        } {
            self.next();
            let target = expr_to_assign_target(lhs)
                .ok_or_else(|| Diagnostic::new("perl", "invalid assignment target", 1, 1))?;
            let rhs = self.parse_expr()?;
            let _ = self.eat(&PTokKind::Semi);
            return Ok(Stmt::Assign {
                id: 0,
                target,
                op,
                value: rhs,
                meta: Metadata::new(),
            });
        }

        let _ = self.eat(&PTokKind::Semi);
        Ok(Stmt::Expr {
            id: 0,
            expr: lhs,
            meta: Metadata::new(),
        })
    }

    fn parse_if_or_match_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&PTokKind::LParen, "'(' after if")?;
        let cond = self.parse_expr()?;
        self.expect(&PTokKind::RParen, "')'")?;
        self.expect(&PTokKind::LBrace, "'{'")?;

        if matches!(self.peek_kind(), Some(PTokKind::Directive(d)) if d == "match") {
            self.next();
            return self.parse_match_block();
        }

        let then_body = self.parse_block_until_rbrace()?;
        let else_body = if self.eat_kw("elsif") {
            vec![self.parse_if_or_match_stmt()?]
        } else if self.eat_kw("else") {
            self.expect(&PTokKind::LBrace, "'{' after else")?;
            self.parse_block_until_rbrace()?
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

    fn parse_match_block(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect_kw("my")?;
        let mvar = self.expect_scalar_var()?;
        self.expect(&PTokKind::Eq, "'='")?;
        let scrutinee = self.parse_expr()?;
        let _ = self.eat(&PTokKind::Semi);

        let mut arms = Vec::new();
        if self.eat_kw("if") {
            loop {
                self.expect(&PTokKind::LParen, "'('")?;
                let cond_expr = self.parse_expr()?;
                self.expect(&PTokKind::RParen, "')'")?;
                self.expect(&PTokKind::LBrace, "'{'")?;
                let pat = extract_perl_match_pat(&cond_expr, &mvar);
                let body = self.parse_block_until_rbrace()?;
                arms.push(MatchArm { pat, body });

                if self.eat_kw("elsif") {
                    continue;
                } else if self.eat_kw("else") {
                    self.expect(&PTokKind::LBrace, "'{'")?;
                    let else_body = self.parse_block_until_rbrace()?;
                    arms.push(MatchArm {
                        pat: MatchPat::Wildcard,
                        body: else_body,
                    });
                    break;
                } else {
                    break;
                }
            }
        }
        self.expect(&PTokKind::RBrace, "'}' after match block")?;
        Ok(Stmt::Match {
            id: 0,
            expr: scrutinee,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_and()?;
        while self.eat(&PTokKind::OrOr) {
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
        while self.eat(&PTokKind::AndAnd) {
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
                Some(PTokKind::EqEq) => Some(BinOp::Eq),
                Some(PTokKind::NotEq) => Some(BinOp::Ne),
                Some(PTokKind::Lt) => Some(BinOp::Lt),
                Some(PTokKind::Le) => Some(BinOp::Le),
                Some(PTokKind::Gt) => Some(BinOp::Gt),
                Some(PTokKind::Ge) => Some(BinOp::Ge),
                Some(PTokKind::Ident(s)) => match s.as_str() {
                    "eq" => Some(BinOp::Eq),
                    "ne" => Some(BinOp::Ne),
                    "lt" => Some(BinOp::Lt),
                    "le" => Some(BinOp::Le),
                    "gt" => Some(BinOp::Gt),
                    "ge" => Some(BinOp::Ge),
                    _ => None,
                },
                _ => None,
            };
            if let Some(bop) = op {
                self.next();
                let right = self.parse_add()?;
                left = Expr::Binary {
                    op: bop,
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
                Some(PTokKind::Plus) | Some(PTokKind::Dot) => Some(BinOp::Add),
                Some(PTokKind::Minus) => Some(BinOp::Sub),
                _ => None,
            };
            if let Some(bop) = op {
                self.next();
                let right = self.parse_mul()?;
                left = Expr::Binary {
                    op: bop,
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
                Some(PTokKind::Percent) => Some(BinOp::Mod),
                _ => None,
            };
            if let Some(bop) = op {
                self.next();
                let right = self.parse_unary()?;
                left = Expr::Binary {
                    op: bop,
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
        if self.eat(&PTokKind::Bang) {
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
        while self.eat(&PTokKind::Arrow) {
            if self.eat(&PTokKind::LBracket) {
                let idx = self.parse_expr()?;
                self.expect(&PTokKind::RBracket, "']'")?;
                base = Expr::Index {
                    base: Box::new(base),
                    index: Box::new(idx),
                };
            } else if self.eat(&PTokKind::LBrace) {
                let field = self.expect_ident()?;
                self.expect(&PTokKind::RBrace, "'}'")?;
                if let Expr::Var(ref name) = base {
                    if self.known_enums.contains(name) {
                        base = Expr::EnumVariant {
                            enum_name: name.clone(),
                            variant: field,
                        };
                        continue;
                    }
                }
                base = Expr::FieldAccess {
                    base: Box::new(base),
                    field,
                };
            } else {
                return self.err("expected '[' or '{' after '->'");
            }
        }
        Ok(base)
    }

    fn parse_primary(&mut self) -> Result<Expr, Diagnostic> {
        if self.eat(&PTokKind::LParen) {
            let e = self.parse_expr()?;
            self.expect(&PTokKind::RParen, "')'")?;
            return Ok(e);
        }

        if self.eat(&PTokKind::LBracket) {
            let mut items = Vec::new();
            while !self.eat(&PTokKind::RBracket) {
                items.push(self.parse_expr()?);
                if !self.eat(&PTokKind::Comma) {
                    self.expect(&PTokKind::RBracket, "']'")?;
                    break;
                }
            }
            return Ok(Expr::List(items));
        }

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
            Some(PTokKind::ScalarVar(name)) => {
                self.next();
                Ok(Expr::Var(name))
            }
            Some(PTokKind::Ident(name)) => {
                self.next();
                if name == "true" {
                    if self.eat(&PTokKind::LParen) {
                        self.expect(&PTokKind::RParen, "')'")?;
                    }
                    return Ok(Expr::Bool(true));
                }
                if name == "false" {
                    if self.eat(&PTokKind::LParen) {
                        self.expect(&PTokKind::RParen, "')'")?;
                    }
                    return Ok(Expr::Bool(false));
                }

                if name == "scalar" && self.eat(&PTokKind::LParen) {
                    self.expect(&PTokKind::At, "'@' inside scalar(...)")?;
                    let inner = if self.eat(&PTokKind::LBrace) {
                        let e = self.parse_expr()?;
                        self.expect(&PTokKind::RBrace, "'}'")?;
                        e
                    } else {
                        let v = self.expect_scalar_var()?;
                        Expr::Var(v)
                    };
                    self.expect(&PTokKind::RParen, "')'")?;
                    return Ok(Expr::Intrinsic(Box::new(Intrinsic::Len(inner))));
                }

                if name == "push" && self.eat(&PTokKind::LParen) {
                    self.expect(&PTokKind::At, "'@' inside push(...)")?;
                    let list = if self.eat(&PTokKind::LBrace) {
                        let e = self.parse_expr()?;
                        self.expect(&PTokKind::RBrace, "'}'")?;
                        e
                    } else {
                        let v = self.expect_scalar_var()?;
                        Expr::Var(v)
                    };
                    self.expect(&PTokKind::Comma, "','")?;
                    let value = self.parse_expr()?;
                    self.expect(&PTokKind::RParen, "')'")?;
                    return Ok(Expr::Intrinsic(Box::new(Intrinsic::Push { list, value })));
                }

                if let Some(struct_name) = name.strip_prefix("new_") {
                    if self.known_structs.contains_key(struct_name) && self.eat(&PTokKind::LParen) {
                        self.expect(&PTokKind::LBrace, "'{'")?;
                        let mut fields = Vec::new();
                        while !self.eat(&PTokKind::RBrace) {
                            let fname = self.expect_ident()?;
                            self.expect(&PTokKind::FatComma, "'=>'")?;
                            let fval = self.parse_expr()?;
                            fields.push((fname, fval));
                            if !self.eat(&PTokKind::Comma) {
                                self.expect(&PTokKind::RBrace, "'}'")?;
                                break;
                            }
                        }
                        self.expect(&PTokKind::RParen, "')'")?;
                        return Ok(Expr::StructInit {
                            name: struct_name.to_string(),
                            fields,
                        });
                    }
                }

                if self.eat(&PTokKind::LParen) {
                    let mut args = Vec::new();
                    while !self.eat(&PTokKind::RParen) {
                        args.push(self.parse_expr()?);
                        if !self.eat(&PTokKind::Comma) {
                            self.expect(&PTokKind::RParen, "')'")?;
                            break;
                        }
                    }

                    match (name.as_str(), args.len()) {
                        ("star_idiv", 2) => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            return Ok(Expr::Binary {
                                op: BinOp::IntDiv,
                                left: Box::new(a),
                                right: Box::new(b),
                            });
                        }
                        ("star_irem", 2) => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            return Ok(Expr::Binary {
                                op: BinOp::Mod,
                                left: Box::new(a),
                                right: Box::new(b),
                            });
                        }
                        ("star_eql", 2) => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            return Ok(Expr::Binary {
                                op: BinOp::Eq,
                                left: Box::new(a),
                                right: Box::new(b),
                            });
                        }
                        ("star_neql", 2) => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            return Ok(Expr::Binary {
                                op: BinOp::Ne,
                                left: Box::new(a),
                                right: Box::new(b),
                            });
                        }
                        ("length", 1) => {
                            return Ok(Expr::Intrinsic(Box::new(Intrinsic::Len(
                                args.pop().unwrap(),
                            ))));
                        }
                        ("min", 2) => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            return Ok(Expr::Intrinsic(Box::new(Intrinsic::Min(a, b))));
                        }
                        ("max", 2) => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            return Ok(Expr::Intrinsic(Box::new(Intrinsic::Max(a, b))));
                        }
                        ("abs", 1) => {
                            return Ok(Expr::Intrinsic(Box::new(Intrinsic::Abs(
                                args.pop().unwrap(),
                            ))));
                        }
                        ("uc", 1) => {
                            return Ok(Expr::Intrinsic(Box::new(Intrinsic::Upper(
                                args.pop().unwrap(),
                            ))));
                        }
                        ("lc", 1) => {
                            return Ok(Expr::Intrinsic(Box::new(Intrinsic::Lower(
                                args.pop().unwrap(),
                            ))));
                        }
                        ("star_tostr", 1) => {
                            return Ok(Expr::Intrinsic(Box::new(Intrinsic::ToStr(
                                args.pop().unwrap(),
                            ))));
                        }
                        ("star_contains", 2) => {
                            let needle = args.pop().unwrap();
                            let haystack = args.pop().unwrap();
                            return Ok(Expr::Intrinsic(Box::new(Intrinsic::Contains {
                                haystack,
                                needle,
                            })));
                        }
                        ("star_print", _) => {
                            return Ok(Expr::Intrinsic(Box::new(Intrinsic::Print(args))));
                        }
                        _ => {
                            return Ok(Expr::Call { func: name, args });
                        }
                    }
                }

                Ok(Expr::Var(name))
            }
            _ => self.err("expected expression in Perl source"),
        }
    }
}

fn extract_perl_match_pat(cond: &Expr, mvar: &str) -> MatchPat {
    if matches!(cond, Expr::Int(1) | Expr::Bool(true)) {
        return MatchPat::Wildcard;
    }
    match cond {
        Expr::Binary {
            op: BinOp::Eq,
            left,
            right,
        } if matches!(left.as_ref(), Expr::Var(v) if v == mvar) => match right.as_ref() {
            Expr::Int(v) => MatchPat::Int(*v),
            Expr::Unary {
                op: UnaryOp::Neg,
                expr: inner,
            } if matches!(inner.as_ref(), Expr::Int(_)) => {
                if let Expr::Int(v) = inner.as_ref() {
                    MatchPat::Int(-v)
                } else {
                    MatchPat::Wildcard
                }
            }
            Expr::Str(s) => MatchPat::Str(s.clone()),
            Expr::EnumVariant { enum_name, variant } => MatchPat::EnumVariant {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
            },
            _ => MatchPat::Wildcard,
        },
        _ => MatchPat::Wildcard,
    }
}

fn unlift_perl_range_hi(raw: Expr) -> Expr {
    match raw {
        Expr::Int(m) if m >= 0 => Expr::Int(m + 1),
        Expr::Binary {
            op: BinOp::Sub,
            left,
            right,
        } if *right == Expr::Int(1) => *left,
        other => Expr::Binary {
            op: BinOp::Add,
            left: Box::new(other),
            right: Box::new(Expr::Int(1)),
        },
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

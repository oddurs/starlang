use std::collections::{HashMap, HashSet};

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl,
    HubModule, Intrinsic, Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl,
    Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct JavaLens;

impl LanguageLens for JavaLens {
    fn id(&self) -> SpokeId {
        SpokeId::Java
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut ctx = JavaEmitter::from_hub(hub);
        let mut out = String::from("import java.util.*;\n\nclass StarProgram {\n");

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

        out.push_str("}\n");
        out
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_java(source)?;
        let mut struct_field_order: HashMap<String, Vec<String>> = HashMap::new();
        let mut known_enums: HashSet<String> = HashSet::new();
        let mut variant_to_enum: HashMap<String, String> = HashMap::new();

        for item in &prev_hub.items {
            match item {
                Item::Struct(s) => {
                    struct_field_order
                        .insert(s.name.clone(), s.fields.iter().map(|f| f.name.clone()).collect());
                }
                Item::Enum(e) => {
                    known_enums.insert(e.name.clone());
                    for v in &e.variants {
                        variant_to_enum.insert(v.clone(), e.name.clone());
                    }
                }
                _ => {}
            }
        }

        prescan_java_types(
            &tokens,
            &mut struct_field_order,
            &mut known_enums,
            &mut variant_to_enum,
        );

        let mut parser = JavaParser {
            tokens,
            pos: 0,
            struct_field_order,
            known_enums,
            variant_to_enum,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Java))
    }
}

struct JavaEmitter {
    local_env: HashMap<String, Type>,
    fn_ret_types: HashMap<String, Type>,
    struct_fields: HashMap<String, HashMap<String, Type>>,
    struct_order: HashMap<String, Vec<String>>,
    enum_names: HashSet<String>,
}

impl JavaEmitter {
    fn from_hub(hub: &HubModule) -> Self {
        let mut fn_ret_types = HashMap::new();
        let mut struct_fields = HashMap::new();
        let mut struct_order = HashMap::new();
        let mut enum_names = HashSet::new();

        for item in &hub.items {
            match item {
                Item::Function(f) => {
                    fn_ret_types.insert(f.name.clone(), f.ret_ty.clone());
                }
                Item::Struct(s) => {
                    let mut map = HashMap::new();
                    let mut ord = Vec::new();
                    for fl in &s.fields {
                        map.insert(fl.name.clone(), fl.ty.clone());
                        ord.push(fl.name.clone());
                    }
                    struct_fields.insert(s.name.clone(), map);
                    struct_order.insert(s.name.clone(), ord);
                }
                Item::Enum(e) => {
                    enum_names.insert(e.name.clone());
                }
                Item::Test(_) => {}
            }
        }

        Self {
            local_env: HashMap::new(),
            fn_ret_types,
            struct_fields,
            struct_order,
            enum_names,
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

    fn is_primitive_or_enum_ty(&self, ty: &Type) -> bool {
        match ty {
            Type::Int | Type::Float | Type::Bool => true,
            Type::Named(n) => self.enum_names.contains(n),
            _ => false,
        }
    }

    fn fmt_type(ty: &Type) -> String {
        match ty {
            Type::Int => "long".to_string(),
            Type::Float => "double".to_string(),
            Type::Bool => "boolean".to_string(),
            Type::Str => "String".to_string(),
            Type::Void => "void".to_string(),
            Type::List(inner) => format!("List<{}>", Self::fmt_boxed_type(inner)),
            Type::Named(name) => name.clone(),
        }
    }

    fn fmt_boxed_type(ty: &Type) -> String {
        match ty {
            Type::Int => "Long".to_string(),
            Type::Float => "Double".to_string(),
            Type::Bool => "Boolean".to_string(),
            Type::Str => "String".to_string(),
            Type::Void => "Void".to_string(),
            Type::List(inner) => format!("List<{}>", Self::fmt_boxed_type(inner)),
            Type::Named(name) => name.clone(),
        }
    }

    fn fmt_struct(&self, s: &StructDecl, out: &mut String) {
        for c in &s.comments {
            out.push_str(&format!("    // {}\n", c));
        }
        out.push_str(&format!("    static final class {} {{\n", s.name));
        for f in &s.fields {
            out.push_str(&format!("        {} {};\n", Self::fmt_type(&f.ty), f.name));
        }
        let ctor_params: Vec<String> = s
            .fields
            .iter()
            .map(|f| format!("{} {}", Self::fmt_type(&f.ty), f.name))
            .collect();
        out.push_str(&format!("\n        {}({}) {{\n", s.name, ctor_params.join(", ")));
        for f in &s.fields {
            out.push_str(&format!("            this.{} = {};\n", f.name, f.name));
        }
        out.push_str("        }\n\n");

        out.push_str("        @Override\n");
        out.push_str("        public boolean equals(Object o) {\n");
        out.push_str(&format!(
            "            if (!(o instanceof {} other)) return false;\n",
            s.name
        ));
        if s.fields.is_empty() {
            out.push_str("            return true;\n");
        } else {
            let eqs: Vec<String> = s
                .fields
                .iter()
                .map(|f| format!("Objects.equals(this.{}, other.{})", f.name, f.name))
                .collect();
            out.push_str(&format!("            return {};\n", eqs.join(" && ")));
        }
        out.push_str("        }\n\n");

        out.push_str("        @Override\n");
        out.push_str("        public int hashCode() {\n");
        let h_args: Vec<String> = s.fields.iter().map(|f| format!("this.{}", f.name)).collect();
        out.push_str(&format!(
            "            return Objects.hash({});\n",
            h_args.join(", ")
        ));
        out.push_str("        }\n");
        out.push_str("    }\n");
    }

    fn fmt_enum(&self, e: &EnumDecl, out: &mut String) {
        for c in &e.comments {
            out.push_str(&format!("    // {}\n", c));
        }
        out.push_str(&format!("    enum {} {{\n", e.name));
        for (i, v) in e.variants.iter().enumerate() {
            let comma = if i + 1 < e.variants.len() { "," } else { "" };
            out.push_str(&format!("        {}{}\n", v, comma));
        }
        out.push_str("    }\n");
    }

    fn fmt_fn(&mut self, f: &FnDecl, out: &mut String) {
        for c in &f.comments {
            out.push_str(&format!("    // {}\n", c));
        }
        self.local_env.clear();
        for p in &f.params {
            self.local_env.insert(p.name.clone(), p.ty.clone());
        }

        if f.name == "main" && f.params.is_empty() {
            out.push_str("    public static void main(String[] args) {\n");
        } else {
            let params_str: Vec<String> = f
                .params
                .iter()
                .map(|p| format!("{} {}", Self::fmt_type(&p.ty), p.name))
                .collect();
            out.push_str(&format!(
                "    static {} {}({}) {{\n",
                Self::fmt_type(&f.ret_ty),
                f.name,
                params_str.join(", ")
            ));
        }

        for stmt in &f.body {
            self.fmt_stmt(stmt, 2, out);
        }
        if f.ret_ty != Type::Void && !stmts_definitely_terminate_java(&f.body) {
            out.push_str("        throw new IllegalStateException(\"unreachable\");\n");
        }
        out.push_str("    }\n");
    }

    fn fmt_test(&mut self, t: &TestDecl, out: &mut String) {
        for c in &t.comments {
            out.push_str(&format!("    // {}\n", c));
        }
        self.local_env.clear();
        out.push_str(&format!("    static void test_{}() {{\n", t.name));
        for stmt in &t.body {
            self.fmt_stmt(stmt, 2, out);
        }
        out.push_str("    }\n");
    }

    fn fmt_pat(pat: &MatchPat) -> String {
        match pat {
            MatchPat::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
            MatchPat::Int(v) => v.to_string(),
            MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
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
                let final_kw = if *mutable { "" } else { "final " };
                if let Some(t) = ty {
                    let val_s = match (t, value) {
                        (Type::List(_), Expr::List(items)) if items.is_empty() => {
                            "new ArrayList<>()".to_string()
                        }
                        _ => self.fmt_expr(value),
                    };
                    self.local_env.insert(name.clone(), t.clone());
                    out.push_str(&format!(
                        "{}{}{} {} = {};\n",
                        pad,
                        final_kw,
                        Self::fmt_type(t),
                        name,
                        val_s
                    ));
                } else if matches!(value, Expr::List(items) if items.is_empty()) {
                    self.local_env
                        .insert(name.clone(), Type::List(Box::new(Type::Int)));
                    out.push_str(&format!(
                        "{}{}List<Long> {} = new ArrayList<>();\n",
                        pad, final_kw, name
                    ));
                } else {
                    if let Some(inferred) = self.expr_ty(value) {
                        self.local_env.insert(name.clone(), inferred);
                    }
                    out.push_str(&format!(
                        "{}{}var {} = {};\n",
                        pad,
                        final_kw,
                        name,
                        self.fmt_expr(value)
                    ));
                }
            }
            Stmt::Assign {
                target, op, value, ..
            } => match target {
                AssignTarget::Index { base, index } => {
                    let idx_s = format!("(int) ({})", self.fmt_expr(index));
                    match op {
                        AssignOp::Set => out.push_str(&format!(
                            "{}{}.set({}, {});\n",
                            pad,
                            base,
                            idx_s,
                            self.fmt_expr(value)
                        )),
                        AssignOp::AddAssign => out.push_str(&format!(
                            "{}{}.set({}, {}.get({}) + ({}));\n",
                            pad,
                            base,
                            idx_s,
                            base,
                            idx_s,
                            self.fmt_expr(value)
                        )),
                        AssignOp::SubAssign => out.push_str(&format!(
                            "{}{}.set({}, {}.get({}) - ({}));\n",
                            pad,
                            base,
                            idx_s,
                            base,
                            idx_s,
                            self.fmt_expr(value)
                        )),
                    }
                }
                AssignTarget::Var(v) => {
                    let op_s = match op {
                        AssignOp::Set => "=",
                        AssignOp::AddAssign => "+=",
                        AssignOp::SubAssign => "-=",
                    };
                    out.push_str(&format!("{}{} {} {};\n", pad, v, op_s, self.fmt_expr(value)));
                }
                AssignTarget::Field { base, field } => {
                    let op_s = match op {
                        AssignOp::Set => "=",
                        AssignOp::AddAssign => "+=",
                        AssignOp::SubAssign => "-=",
                    };
                    out.push_str(&format!(
                        "{}{}.{} {} {};\n",
                        pad,
                        base,
                        field,
                        op_s,
                        self.fmt_expr(value)
                    ));
                }
            },
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.fmt_if_chain(cond, then_body, else_body, indent, true, out);
            }
            Stmt::Match { expr, arms, .. } => {
                let is_int_switch = arms.iter().any(|a| matches!(a.pat, MatchPat::Int(_)))
                    || self.expr_ty(expr) == Some(Type::Int);
                let scrutinee = if is_int_switch {
                    format!("(int) ({})", self.fmt_expr(expr))
                } else {
                    self.fmt_expr(expr)
                };
                out.push_str(&format!("{}switch ({}) {{\n", pad, scrutinee));
                for arm in arms {
                    if arm.pat == MatchPat::Wildcard {
                        out.push_str(&format!("{}    default -> {{\n", pad));
                    } else {
                        out.push_str(&format!(
                            "{}    case {} -> {{\n",
                            pad,
                            Self::fmt_pat(&arm.pat)
                        ));
                    }
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
                    "{}for (var {} : {}) {{\n",
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
                    "{}for (long {} = {}; {} < {}; {}++) {{\n",
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
                    "{}if (!({})) {{ throw new AssertionError(\"assertion failed\"); }}\n",
                    pad,
                    self.fmt_expr(cond)
                ));
            }
            Stmt::AssertEq { left, right, .. } => {
                out.push_str(&format!(
                    "{}if (!Objects.equals({}, {})) {{ throw new AssertionError(\"assert_eq failed\"); }}\n",
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

    fn fmt_if_chain(
        &mut self,
        cond: &Expr,
        then_body: &[Stmt],
        else_body: &[Stmt],
        indent: usize,
        is_first: bool,
        out: &mut String,
    ) {
        let pad = "    ".repeat(indent);
        if is_first {
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
            let saved = self.local_env.clone();
            for s in else_body {
                self.fmt_stmt(s, indent + 1, out);
            }
            self.local_env = saved;
            out.push_str(&format!("{}}}\n", pad));
        }
    }

    fn fmt_postfix(&self, expr: &Expr) -> String {
        match expr {
            Expr::Binary { .. } | Expr::Unary { .. } => format!("({})", self.fmt_expr(expr)),
            Expr::Int(v) if *v < 0 => format!("({}L)", v),
            Expr::Float(v) if *v < 0.0 => format!("({})", format_float(*v)),
            _ => self.fmt_expr(expr),
        }
    }

    fn fmt_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => format!("{}L", v),
            Expr::Float(v) => format_float(*v),
            Expr::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Expr::Str(s) => format!("\"{}\"", escape_str(s)),
            Expr::Var(name) => name.clone(),
            Expr::List(items) => {
                if items.is_empty() {
                    "new ArrayList<>()".to_string()
                } else {
                    let inner: Vec<String> = items.iter().map(|e| self.fmt_expr(e)).collect();
                    format!("new ArrayList<>(Arrays.asList({}))", inner.join(", "))
                }
            }
            Expr::StructInit { name, fields } => {
                let ordered_vals: Vec<String> =
                    if let Some(decl_order) = self.struct_order.get(name) {
                        let mut out_v = Vec::with_capacity(fields.len());
                        for df in decl_order {
                            if let Some((_, val)) = fields.iter().find(|(k, _)| k == df) {
                                out_v.push(self.fmt_expr(val));
                            }
                        }
                        for (k, val) in fields {
                            if !decl_order.contains(k) {
                                out_v.push(self.fmt_expr(val));
                            }
                        }
                        out_v
                    } else {
                        fields.iter().map(|(_, v)| self.fmt_expr(v)).collect()
                    };
                format!("new {}({})", name, ordered_vals.join(", "))
            }
            Expr::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
            Expr::FieldAccess { base, field } => {
                format!("{}.{}", self.fmt_postfix(base), field)
            }
            Expr::Index { base, index } => {
                format!("{}.get((int) ({}))", self.fmt_postfix(base), self.fmt_expr(index))
            }
            Expr::Unary { op, expr: inner } => {
                let inner_s = if matches!(inner.as_ref(), Expr::Binary { .. } | Expr::Unary { .. })
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
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    let lt = self.expr_ty(left);
                    let rt = self.expr_ty(right);
                    let both_prim = match (&lt, &rt) {
                        (Some(a), Some(b)) => {
                            self.is_primitive_or_enum_ty(a) && self.is_primitive_or_enum_ty(b)
                        }
                        _ => false,
                    };
                    if !both_prim {
                        if *op == BinOp::Eq {
                            return format!(
                                "Objects.equals({}, {})",
                                self.fmt_expr(left),
                                self.fmt_expr(right)
                            );
                        } else {
                            return format!(
                                "!Objects.equals({}, {})",
                                self.fmt_expr(left),
                                self.fmt_expr(right)
                            );
                        }
                    }
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
                let a: Vec<String> = args.iter().map(|e| self.fmt_expr(e)).collect();
                format!("{}({})", func, a.join(", "))
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e) => {
                    if self.expr_ty(e) == Some(Type::Str) {
                        format!("((long) {}.length())", self.fmt_postfix(e))
                    } else {
                        format!("((long) {}.size())", self.fmt_postfix(e))
                    }
                }
                Intrinsic::Min(a, b) => {
                    format!("Math.min({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Max(a, b) => {
                    format!("Math.max({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Abs(a) => format!("Math.abs({})", self.fmt_expr(a)),
                Intrinsic::Push { list, value } => {
                    format!("{}.add({})", self.fmt_postfix(list), self.fmt_expr(value))
                }
                Intrinsic::Print(args) => match args.len() {
                    0 => "System.out.println()".to_string(),
                    1 => format!("System.out.println({})", self.fmt_expr(&args[0])),
                    _ => {
                        let wrapped: Vec<String> = args
                            .iter()
                            .map(|a| format!("String.valueOf({})", self.fmt_expr(a)))
                            .collect();
                        format!(
                            "System.out.println(String.join(\" \", {}))",
                            wrapped.join(", ")
                        )
                    }
                },
                Intrinsic::Contains { haystack, needle } => {
                    format!(
                        "{}.contains({})",
                        self.fmt_postfix(haystack),
                        self.fmt_expr(needle)
                    )
                }
                Intrinsic::Upper(e) => format!("{}.toUpperCase()", self.fmt_postfix(e)),
                Intrinsic::Lower(e) => format!("{}.toLowerCase()", self.fmt_postfix(e)),
                Intrinsic::ToStr(e) => format!("String.valueOf({})", self.fmt_expr(e)),
            },
        }
    }
}

/// JLS §14.22 reachability check so `javac` never sees either missing-return or unreachable-statement.
fn stmts_definitely_terminate_java(stmts: &[Stmt]) -> bool {
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
                && stmts_definitely_terminate_java(then_body)
                && stmts_definitely_terminate_java(else_body)
        }
        Stmt::Match { arms, .. } => {
            arms.iter().any(|a| a.pat == MatchPat::Wildcard)
                && arms.iter().all(|a| stmts_definitely_terminate_java(&a.body))
        }
        _ => false,
    }
}

// ============================================================================
// Java 21+ Lexer & Recursive-Descent Parser
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
enum JavaTokKind {
    Ident(String),
    Int(i64),
    Float(f64),
    Str(String),
    Comment(String),
    At,
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
    Dot,
    Plus,
    PlusPlus,
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
struct JavaTok {
    kind: JavaTokKind,
    line: usize,
    col: usize,
}

fn lex_java(src: &str) -> Result<Vec<JavaTok>, Diagnostic> {
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
            tokens.push(JavaTok {
                kind: JavaTokKind::Comment(text.trim().to_string()),
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
                    "java",
                    "unterminated string literal",
                    s_line,
                    s_col,
                ));
            }
            let raw: String = chars[start..i].iter().collect();
            i += 1;
            col += 1;
            tokens.push(JavaTok {
                kind: JavaTokKind::Str(unescape_string(&raw)),
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
            let num_s: String = chars[start..i].iter().filter(|c| **c != '_').collect();
            // Optional `L`/`l`/`D`/`d` suffix
            if i < chars.len() && matches!(chars[i], 'L' | 'l' | 'D' | 'd' | 'F' | 'f') {
                if matches!(chars[i], 'D' | 'd' | 'F' | 'f') {
                    is_float = true;
                }
                i += 1;
                col += 1;
            }
            if is_float {
                let v = num_s.parse::<f64>().map_err(|_| {
                    Diagnostic::new(
                        "java",
                        format!("invalid float literal '{}'", num_s),
                        line,
                        s_col,
                    )
                })?;
                tokens.push(JavaTok {
                    kind: JavaTokKind::Float(v),
                    line,
                    col: s_col,
                });
            } else {
                let v = num_s.parse::<i64>().map_err(|_| {
                    Diagnostic::new(
                        "java",
                        format!("invalid integer literal '{}'", num_s),
                        line,
                        s_col,
                    )
                })?;
                tokens.push(JavaTok {
                    kind: JavaTokKind::Int(v),
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
            tokens.push(JavaTok {
                kind: JavaTokKind::Ident(ident),
                line,
                col: s_col,
            });
            continue;
        }

        let s_col = col;
        if i + 1 < chars.len() {
            let two = match (chars[i], chars[i + 1]) {
                ('-', '>') => Some(JavaTokKind::Arrow),
                ('+', '+') => Some(JavaTokKind::PlusPlus),
                ('&', '&') => Some(JavaTokKind::AmpAmp),
                ('|', '|') => Some(JavaTokKind::PipePipe),
                ('=', '=') => Some(JavaTokKind::EqEq),
                ('!', '=') => Some(JavaTokKind::BangEq),
                ('<', '=') => Some(JavaTokKind::Le),
                ('>', '=') => Some(JavaTokKind::Ge),
                ('+', '=') => Some(JavaTokKind::PlusEq),
                ('-', '=') => Some(JavaTokKind::MinusEq),
                _ => None,
            };
            if let Some(kind) = two {
                tokens.push(JavaTok {
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
            '@' => JavaTokKind::At,
            '(' => JavaTokKind::LParen,
            ')' => JavaTokKind::RParen,
            '{' => JavaTokKind::LBrace,
            '}' => JavaTokKind::RBrace,
            '[' => JavaTokKind::LBracket,
            ']' => JavaTokKind::RBracket,
            ',' => JavaTokKind::Comma,
            ';' => JavaTokKind::Semi,
            ':' => JavaTokKind::Colon,
            '.' => JavaTokKind::Dot,
            '+' => JavaTokKind::Plus,
            '-' => JavaTokKind::Minus,
            '*' => JavaTokKind::Star,
            '/' => JavaTokKind::Slash,
            '%' => JavaTokKind::Percent,
            '!' => JavaTokKind::Bang,
            '=' => JavaTokKind::Eq,
            '<' => JavaTokKind::Lt,
            '>' => JavaTokKind::Gt,
            other => {
                return Err(Diagnostic::new(
                    "java",
                    format!("unexpected character '{}'", other),
                    line,
                    s_col,
                ))
            }
        };
        tokens.push(JavaTok {
            kind,
            line,
            col: s_col,
        });
        i += 1;
        col += 1;
    }

    Ok(tokens)
}

/// Pre-scan nested `static class` / `record` / `enum` declarations so forward references
/// to `new Struct(...)` and `Enum.Variant` resolve even on cold `put`.
fn prescan_java_types(
    tokens: &[JavaTok],
    struct_field_order: &mut HashMap<String, Vec<String>>,
    known_enums: &mut HashSet<String>,
    variant_to_enum: &mut HashMap<String, String>,
) {
    let mut brace_depth = 0usize;
    let mut i = 0;
    while i < tokens.len() {
        match &tokens[i].kind {
            JavaTokKind::LBrace => {
                brace_depth += 1;
                i += 1;
            }
            JavaTokKind::RBrace => {
                brace_depth = brace_depth.saturating_sub(1);
                i += 1;
            }
            JavaTokKind::Ident(kw) if kw == "enum" && brace_depth >= 1 => {
                if let Some(JavaTok {
                    kind: JavaTokKind::Ident(ename),
                    ..
                }) = tokens.get(i + 1)
                {
                    known_enums.insert(ename.clone());
                    if matches!(tokens.get(i + 2).map(|t| &t.kind), Some(JavaTokKind::LBrace)) {
                        let mut j = i + 3;
                        while j < tokens.len()
                            && !matches!(tokens[j].kind, JavaTokKind::RBrace | JavaTokKind::Semi)
                        {
                            if let JavaTokKind::Ident(v) = &tokens[j].kind {
                                variant_to_enum.insert(v.clone(), ename.clone());
                            }
                            j += 1;
                        }
                    }
                }
                i += 1;
            }
            JavaTokKind::Ident(kw) if kw == "class" && brace_depth == 1 => {
                if let Some(JavaTok {
                    kind: JavaTokKind::Ident(sname),
                    ..
                }) = tokens.get(i + 1)
                {
                    if matches!(tokens.get(i + 2).map(|t| &t.kind), Some(JavaTokKind::LBrace)) {
                        let mut fields = Vec::new();
                        let mut j = i + 3;
                        let mut sub_depth = 1usize;
                        while j < tokens.len() && sub_depth > 0 {
                            match &tokens[j].kind {
                                JavaTokKind::LBrace => sub_depth += 1,
                                JavaTokKind::RBrace => sub_depth -= 1,
                                // Field declaration at sub_depth == 1 ends with `;`: `<Type> <fname>;`
                                JavaTokKind::Semi if sub_depth == 1 && j >= 2 => {
                                    if let JavaTokKind::Ident(fname) = &tokens[j - 1].kind {
                                        if !matches!(
                                            tokens[j - 2].kind,
                                            JavaTokKind::RParen | JavaTokKind::Ident(_)
                                        ) || matches!(tokens[j - 2].kind, JavaTokKind::Ident(_) | JavaTokKind::Gt)
                                        {
                                            if fname != "return" && fname != "false" && fname != "true" {
                                                fields.push(fname.clone());
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                            j += 1;
                        }
                        struct_field_order.entry(sname.clone()).or_insert(fields);
                    }
                }
                i += 1;
            }
            JavaTokKind::Ident(kw) if kw == "record" && brace_depth >= 1 => {
                if let Some(JavaTok {
                    kind: JavaTokKind::Ident(sname),
                    ..
                }) = tokens.get(i + 1)
                {
                    if matches!(tokens.get(i + 2).map(|t| &t.kind), Some(JavaTokKind::LParen)) {
                        let mut fields = Vec::new();
                        let mut j = i + 3;
                        while j < tokens.len() && !matches!(tokens[j].kind, JavaTokKind::RParen) {
                            if matches!(
                                tokens.get(j + 1).map(|t| &t.kind),
                                Some(JavaTokKind::Comma | JavaTokKind::RParen)
                            ) {
                                if let JavaTokKind::Ident(fname) = &tokens[j].kind {
                                    fields.push(fname.clone());
                                }
                            }
                            j += 1;
                        }
                        struct_field_order.insert(sname.clone(), fields);
                    }
                }
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }
}

struct JavaParser {
    tokens: Vec<JavaTok>,
    pos: usize,
    struct_field_order: HashMap<String, Vec<String>>,
    known_enums: HashSet<String>,
    variant_to_enum: HashMap<String, String>,
}

impl JavaParser {
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
        Err(Diagnostic::new("java", msg, l, c))
    }

    fn peek_kind(&self) -> Option<&JavaTokKind> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn peek_kind_at(&self, offset: usize) -> Option<&JavaTokKind> {
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<JavaTok> {
        let tok = self.tokens.get(self.pos).cloned();
        if tok.is_some() {
            self.pos += 1;
        }
        tok
    }

    fn eat(&mut self, expected: &JavaTokKind) -> bool {
        if self.peek_kind() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if matches!(self.peek_kind(), Some(JavaTokKind::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &JavaTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(expected) {
            Ok(())
        } else {
            self.err(format!("expected {}", label))
        }
    }

    fn expect_ident(&mut self) -> Result<String, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(JavaTokKind::Ident(s)) => {
                self.pos += 1;
                Ok(s)
            }
            _ => self.err("expected identifier"),
        }
    }

    fn take_comments(&mut self) -> Vec<String> {
        let mut out = Vec::new();
        while let Some(JavaTokKind::Comment(c)) = self.peek_kind().cloned() {
            self.pos += 1;
            out.push(c);
        }
        out
    }

    fn skip_balanced_braces(&mut self) -> Result<(), Diagnostic> {
        self.expect(&JavaTokKind::LBrace, "'{'")?;
        let mut depth = 1usize;
        while depth > 0 {
            match self.next().map(|t| t.kind) {
                Some(JavaTokKind::LBrace) => depth += 1,
                Some(JavaTokKind::RBrace) => depth -= 1,
                Some(_) => {}
                None => return self.err("unclosed '{'"),
            }
        }
        Ok(())
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let _ = self.take_comments();
        // Skip optional `package ...;` and `import ...;`
        while self.eat_kw("package") || self.eat_kw("import") {
            while !matches!(self.peek_kind(), Some(JavaTokKind::Semi) | None) {
                self.pos += 1;
            }
            self.expect(&JavaTokKind::Semi, "';'")?;
            let _ = self.take_comments();
        }

        while self.eat_kw("public") || self.eat_kw("final") {
            // outer class modifiers
        }
        if !self.eat_kw("class") {
            return self.err("expected outer 'class' declaration in Java module");
        }
        let _outer_name = self.expect_ident()?;
        self.expect(&JavaTokKind::LBrace, "'{'")?;

        let mut items = Vec::new();
        while !matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
            let _ = self.eat(&JavaTokKind::Semi);
            let comments = self.take_comments();
            if matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
                break;
            }
            while self.eat_kw("public")
                || self.eat_kw("private")
                || self.eat_kw("protected")
                || self.eat_kw("static")
                || self.eat_kw("final")
            {}

            if self.eat_kw("class") {
                items.push(Item::Struct(self.parse_struct_class(comments)?));
            } else if self.eat_kw("record") {
                items.push(Item::Struct(self.parse_record(comments)?));
            } else if self.eat_kw("enum") {
                items.push(Item::Enum(self.parse_enum(comments)?));
            } else {
                items.push(self.parse_method_or_test(comments)?);
            }
        }
        self.expect(&JavaTokKind::RBrace, "'}'")?;

        Ok(HubModule {
            next_id: 1,
            items,
        })
    }

    fn parse_struct_class(&mut self, comments: Vec<String>) -> Result<StructDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&JavaTokKind::LBrace, "'{'")?;
        let mut fields = Vec::new();

        while !matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
            let _ = self.take_comments();
            if matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
                break;
            }
            // Skip `@Override ...` methods (`equals`, `hashCode`, `toString`)
            while self.eat(&JavaTokKind::At) {
                let _ = self.expect_ident()?;
            }
            while self.eat_kw("public") || self.eat_kw("private") || self.eat_kw("final") {}

            // Constructor `Name(...) { ... }`
            if matches!(self.peek_kind(), Some(JavaTokKind::Ident(s)) if s == &name)
                && matches!(self.peek_kind_at(1), Some(JavaTokKind::LParen))
            {
                self.pos += 2;
                while !matches!(self.peek_kind(), Some(JavaTokKind::RParen) | None) {
                    self.pos += 1;
                }
                self.expect(&JavaTokKind::RParen, "')'")?;
                self.skip_balanced_braces()?;
                continue;
            }

            let ty = self.parse_type()?;
            let member_name = self.expect_ident()?;
            if self.eat(&JavaTokKind::LParen) {
                // Method inside struct (`equals`, `hashCode`, etc.) -> skip
                while !matches!(self.peek_kind(), Some(JavaTokKind::RParen) | None) {
                    self.pos += 1;
                }
                self.expect(&JavaTokKind::RParen, "')'")?;
                self.skip_balanced_braces()?;
            } else {
                self.expect(&JavaTokKind::Semi, "';'")?;
                fields.push(Field {
                    id: 0,
                    name: member_name,
                    ty,
                    meta: Metadata::new(),
                });
            }
        }
        self.expect(&JavaTokKind::RBrace, "'}'")?;
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

    fn parse_record(&mut self, comments: Vec<String>) -> Result<StructDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.expect(&JavaTokKind::LParen, "'('")?;
        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), Some(JavaTokKind::RParen) | None) {
            let fty = self.parse_type()?;
            let fname = self.expect_ident()?;
            fields.push(Field {
                id: 0,
                name: fname,
                ty: fty,
                meta: Metadata::new(),
            });
            if !self.eat(&JavaTokKind::Comma) {
                break;
            }
        }
        self.expect(&JavaTokKind::RParen, "')'")?;
        self.skip_balanced_braces()?;
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

    fn parse_enum(&mut self, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        let name = self.expect_ident()?;
        self.known_enums.insert(name.clone());
        self.expect(&JavaTokKind::LBrace, "'{'")?;
        let mut variants = Vec::new();
        while !matches!(
            self.peek_kind(),
            Some(JavaTokKind::RBrace | JavaTokKind::Semi) | None
        ) {
            let _ = self.take_comments();
            if matches!(
                self.peek_kind(),
                Some(JavaTokKind::RBrace | JavaTokKind::Semi) | None
            ) {
                break;
            }
            let v = self.expect_ident()?;
            self.variant_to_enum.insert(v.clone(), name.clone());
            variants.push(v);
            let _ = self.eat(&JavaTokKind::Comma);
        }
        if self.eat(&JavaTokKind::Semi) {
            while !matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
                self.pos += 1;
            }
        }
        self.expect(&JavaTokKind::RBrace, "'}'")?;
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_method_or_test(&mut self, comments: Vec<String>) -> Result<Item, Diagnostic> {
        let ret_ty = self.parse_type()?;
        let name = self.expect_ident()?;
        self.expect(&JavaTokKind::LParen, "'('")?;
        let mut params = Vec::new();

        // Special-case `public static void main(String[] args)` -> `main()` with 0 Hub params
        if name == "main"
            && matches!(self.peek_kind(), Some(JavaTokKind::Ident(s)) if s == "String")
            && matches!(self.peek_kind_at(1), Some(JavaTokKind::LBracket))
        {
            while !matches!(self.peek_kind(), Some(JavaTokKind::RParen) | None) {
                self.pos += 1;
            }
        } else {
            while !matches!(self.peek_kind(), Some(JavaTokKind::RParen) | None) {
                let _ = self.eat_kw("final");
                let pty = self.parse_type()?;
                let pname = self.expect_ident()?;
                params.push(Param {
                    id: 0,
                    name: pname,
                    ty: pty,
                    meta: Metadata::new(),
                });
                if !self.eat(&JavaTokKind::Comma) {
                    break;
                }
            }
        }
        self.expect(&JavaTokKind::RParen, "')'")?;
        let body = self.parse_block()?;

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
        let ident = self.expect_ident()?;
        if (ident == "List" || ident == "ArrayList") && self.eat(&JavaTokKind::Lt) {
            let inner = self.parse_type()?;
            self.expect(&JavaTokKind::Gt, "'>'")?;
            return Ok(Type::List(Box::new(inner)));
        }
        let mut base = match ident.as_str() {
            "long" | "Long" | "int" | "Integer" => Type::Int,
            "double" | "Double" | "float" | "Float" => Type::Float,
            "boolean" | "Boolean" => Type::Bool,
            "String" => Type::Str,
            "void" | "Void" => Type::Void,
            other => Type::Named(other.to_string()),
        };
        while self.eat(&JavaTokKind::LBracket) {
            self.expect(&JavaTokKind::RBracket, "']'")?;
            base = Type::List(Box::new(base));
        }
        Ok(base)
    }

    fn is_local_var_decl(&self) -> bool {
        let mut idx = self.pos;
        if matches!(self.tokens.get(idx).map(|t| &t.kind), Some(JavaTokKind::Ident(s)) if s == "final") {
            idx += 1;
        }
        let Some(JavaTok {
            kind: JavaTokKind::Ident(tname),
            ..
        }) = self.tokens.get(idx)
        else {
            return false;
        };
        if matches!(
            tname.as_str(),
            "if" | "while" | "for" | "switch" | "return" | "break" | "continue" | "throw" | "assert"
        ) {
            return false;
        }
        if tname == "var" {
            return matches!(
                self.tokens.get(idx + 1).map(|t| &t.kind),
                Some(JavaTokKind::Ident(_))
            );
        }
        if tname == "List" || tname == "ArrayList" {
            if matches!(self.tokens.get(idx + 1).map(|t| &t.kind), Some(JavaTokKind::Lt)) {
                let mut depth = 1usize;
                let mut k = idx + 2;
                while k < self.tokens.len() && depth > 0 {
                    match self.tokens[k].kind {
                        JavaTokKind::Lt => depth += 1,
                        JavaTokKind::Gt => depth -= 1,
                        _ => {}
                    }
                    k += 1;
                }
                return matches!(
                    self.tokens.get(k).map(|t| &t.kind),
                    Some(JavaTokKind::Ident(_))
                );
            }
        }
        // `<TypeIdent> <varName> =`
        matches!(
            self.tokens.get(idx + 1).map(|t| &t.kind),
            Some(JavaTokKind::Ident(_))
        ) && matches!(
            self.tokens.get(idx + 2).map(|t| &t.kind),
            Some(JavaTokKind::Eq | JavaTokKind::Semi)
        )
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        self.expect(&JavaTokKind::LBrace, "'{'")?;
        let mut stmts = Vec::new();
        while !matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
            let _ = self.eat(&JavaTokKind::Semi);
            if matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
                break;
            }
            if let Some(stmt) = self.parse_stmt()? {
                stmts.push(stmt);
            }
        }
        self.expect(&JavaTokKind::RBrace, "'}'")?;
        Ok(stmts)
    }

    fn parse_stmt(&mut self) -> Result<Option<Stmt>, Diagnostic> {
        if let Some(JavaTokKind::Comment(text)) = self.peek_kind().cloned() {
            self.pos += 1;
            return Ok(Some(Stmt::Comment { id: 0, text }));
        }
        // Skip synthetic `throw new IllegalStateException("unreachable");`
        if self.eat_kw("throw") {
            while !matches!(self.peek_kind(), Some(JavaTokKind::Semi) | None) {
                self.pos += 1;
            }
            self.expect(&JavaTokKind::Semi, "';'")?;
            return Ok(None);
        }
        if self.eat_kw("if") {
            return self.parse_if().map(Some);
        }
        if self.eat_kw("switch") {
            return self.parse_switch().map(Some);
        }
        if self.eat_kw("while") {
            self.expect(&JavaTokKind::LParen, "'('")?;
            let cond = self.parse_expr()?;
            self.expect(&JavaTokKind::RParen, "')'")?;
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
            self.expect(&JavaTokKind::Semi, "';'")?;
            return Ok(Some(Stmt::Break { id: 0 }));
        }
        if self.eat_kw("continue") {
            self.expect(&JavaTokKind::Semi, "';'")?;
            return Ok(Some(Stmt::Continue { id: 0 }));
        }
        if self.eat_kw("return") {
            if self.eat(&JavaTokKind::Semi) {
                return Ok(Some(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                }));
            }
            let val = self.parse_expr()?;
            self.expect(&JavaTokKind::Semi, "';'")?;
            return Ok(Some(Stmt::Return {
                id: 0,
                value: Some(val),
                meta: Metadata::new(),
            }));
        }
        if self.eat_kw("assert") {
            let cond = self.parse_expr()?;
            if self.eat(&JavaTokKind::Colon) {
                let _ = self.parse_expr()?;
            }
            self.expect(&JavaTokKind::Semi, "';'")?;
            return Ok(Some(Stmt::Assert {
                id: 0,
                cond,
                meta: Metadata::new(),
            }));
        }
        if self.is_local_var_decl() {
            return self.parse_local_let().map(Some);
        }

        // Check `list.set((int) (idx), val);` before general expression parsing
        if let Some(JavaTokKind::Ident(base_name)) = self.peek_kind().cloned() {
            if matches!(self.peek_kind_at(1), Some(JavaTokKind::Dot))
                && matches!(self.peek_kind_at(2), Some(JavaTokKind::Ident(m)) if m == "set")
                && matches!(self.peek_kind_at(3), Some(JavaTokKind::LParen))
            {
                self.pos += 4;
                let idx_expr = self.parse_expr()?;
                self.expect(&JavaTokKind::Comma, "','")?;
                let val_expr = self.parse_expr()?;
                self.expect(&JavaTokKind::RParen, "')'")?;
                self.expect(&JavaTokKind::Semi, "';'")?;
                return Ok(Some(Stmt::Assign {
                    id: 0,
                    target: AssignTarget::Index {
                        base: base_name,
                        index: idx_expr,
                    },
                    op: AssignOp::Set,
                    value: val_expr,
                    meta: Metadata::new(),
                }));
            }
        }

        let expr = self.parse_expr()?;
        if let Some(op) = match self.peek_kind() {
            Some(JavaTokKind::Eq) => Some(AssignOp::Set),
            Some(JavaTokKind::PlusEq) => Some(AssignOp::AddAssign),
            Some(JavaTokKind::MinusEq) => Some(AssignOp::SubAssign),
            _ => None,
        } {
            self.pos += 1;
            let value = self.parse_expr()?;
            self.expect(&JavaTokKind::Semi, "';'")?;
            let target = expr_to_assign_target(expr).ok_or_else(|| {
                let (l, c) = self.cur_loc();
                Diagnostic::new("java", "invalid assignment target", l, c)
            })?;
            return Ok(Some(Stmt::Assign {
                id: 0,
                target,
                op,
                value,
                meta: Metadata::new(),
            }));
        }

        self.expect(&JavaTokKind::Semi, "';'")?;
        Ok(Some(Stmt::Expr {
            id: 0,
            expr,
            meta: Metadata::new(),
        }))
    }

    fn parse_local_let(&mut self) -> Result<Stmt, Diagnostic> {
        let mutable = !self.eat_kw("final");
        let ty = if self.eat_kw("var") {
            None
        } else {
            Some(self.parse_type()?)
        };
        let name = self.expect_ident()?;
        self.expect(&JavaTokKind::Eq, "'='")?;
        let value = self.parse_expr()?;
        self.expect(&JavaTokKind::Semi, "';'")?;
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
        self.expect(&JavaTokKind::LParen, "'('")?;
        let cond = self.parse_expr()?;
        self.expect(&JavaTokKind::RParen, "')'")?;

        // Detect `if (!(c)) { throw new AssertionError(...); }` OR braceless `if (...) throw ...;`
        let braced_throw = matches!(self.peek_kind(), Some(JavaTokKind::LBrace))
            && matches!(self.peek_kind_at(1), Some(JavaTokKind::Ident(s)) if s == "throw");
        let bare_throw = matches!(self.peek_kind(), Some(JavaTokKind::Ident(s)) if s == "throw");
        if braced_throw || bare_throw {
            let mut is_assert_eq = false;
            if braced_throw {
                let mut k = self.pos + 1;
                while k < self.tokens.len() && !matches!(self.tokens[k].kind, JavaTokKind::RBrace) {
                    if let JavaTokKind::Str(msg) = &self.tokens[k].kind {
                        if msg.contains("assert_eq") {
                            is_assert_eq = true;
                        }
                    }
                    k += 1;
                }
                self.skip_balanced_braces()?;
            } else {
                while !matches!(self.peek_kind(), Some(JavaTokKind::Semi) | None) {
                    if let Some(JavaTokKind::Str(msg)) = self.peek_kind() {
                        if msg.contains("assert_eq") {
                            is_assert_eq = true;
                        }
                    }
                    self.pos += 1;
                }
                self.expect(&JavaTokKind::Semi, "';'")?;
            }

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
        self.expect(&JavaTokKind::LParen, "'('")?;
        let expr = self.parse_expr()?;
        self.expect(&JavaTokKind::RParen, "')'")?;
        self.expect(&JavaTokKind::LBrace, "'{'")?;

        let mut arms = Vec::new();
        while !matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
            let _ = self.take_comments();
            if matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
                break;
            }
            let pat = if self.eat_kw("default") {
                MatchPat::Wildcard
            } else if self.eat_kw("case") {
                self.parse_match_pat()?
            } else {
                return self.err("expected 'case' or 'default' in Java switch");
            };

            let body = if self.eat(&JavaTokKind::Arrow) {
                if matches!(self.peek_kind(), Some(JavaTokKind::LBrace)) {
                    self.parse_block()?
                } else if let Some(s) = self.parse_stmt()? {
                    vec![s]
                } else {
                    Vec::new()
                }
            } else {
                self.expect(&JavaTokKind::Colon, "':'")?;
                let mut stmts = Vec::new();
                while !matches!(self.peek_kind(), Some(JavaTokKind::RBrace) | None) {
                    if matches!(
                        self.peek_kind(),
                        Some(JavaTokKind::Ident(s)) if s == "case" || s == "default"
                    ) {
                        break;
                    }
                    if let Some(s) = self.parse_stmt()? {
                        if matches!(s, Stmt::Break { .. }) {
                            break;
                        }
                        stmts.push(s);
                    }
                }
                stmts
            };
            arms.push(MatchArm { pat, body });
        }

        self.expect(&JavaTokKind::RBrace, "'}'")?;
        Ok(Stmt::Match {
            id: 0,
            expr,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_match_pat(&mut self) -> Result<MatchPat, Diagnostic> {
        if self.eat(&JavaTokKind::Minus) {
            if let Some(JavaTokKind::Int(v)) = self.peek_kind().cloned() {
                self.pos += 1;
                return Ok(MatchPat::Int(-v));
            }
            return self.err("expected integer literal after '-' in case pattern");
        }
        match self.peek_kind().cloned() {
            Some(JavaTokKind::Int(v)) => {
                self.pos += 1;
                Ok(MatchPat::Int(v))
            }
            Some(JavaTokKind::Str(s)) => {
                self.pos += 1;
                Ok(MatchPat::Str(s))
            }
            Some(JavaTokKind::Ident(first)) => {
                self.pos += 1;
                if self.eat(&JavaTokKind::Dot) {
                    let variant = self.expect_ident()?;
                    Ok(MatchPat::EnumVariant {
                        enum_name: first,
                        variant,
                    })
                } else {
                    let enum_name = self
                        .variant_to_enum
                        .get(&first)
                        .cloned()
                        .unwrap_or_default();
                    Ok(MatchPat::EnumVariant {
                        enum_name,
                        variant: first,
                    })
                }
            }
            _ => self.err("unsupported Java switch case pattern"),
        }
    }

    fn parse_for(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&JavaTokKind::LParen, "'('")?;
        let _ = self.eat_kw("final");
        let _ = if self.eat_kw("var") {
            None
        } else {
            Some(self.parse_type()?)
        };
        let var = self.expect_ident()?;

        if self.eat(&JavaTokKind::Colon) {
            let iter = self.parse_expr()?;
            self.expect(&JavaTokKind::RParen, "')'")?;
            let body = self.parse_block()?;
            return Ok(Stmt::ForEach {
                id: 0,
                var,
                iter,
                body,
                meta: Metadata::new(),
            });
        }

        // C-style `for (long i = start; i < end; i++)`
        self.expect(&JavaTokKind::Eq, "'='")?;
        let start = self.parse_expr()?;
        self.expect(&JavaTokKind::Semi, "';'")?;
        let cond_var = self.expect_ident()?;
        if cond_var != var {
            return self.err("expected loop variable in for-range condition");
        }
        self.expect(&JavaTokKind::Lt, "'<'")?;
        let end = self.parse_expr()?;
        self.expect(&JavaTokKind::Semi, "';'")?;
        let inc_var = self.expect_ident()?;
        if inc_var != var {
            return self.err("expected loop variable in for-range increment");
        }
        if !self.eat(&JavaTokKind::PlusPlus) {
            self.expect(&JavaTokKind::PlusEq, "'++' or '+='")?;
            let _ = self.parse_expr()?;
        }
        self.expect(&JavaTokKind::RParen, "')'")?;
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
        while self.eat(&JavaTokKind::PipePipe) {
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
        while self.eat(&JavaTokKind::AmpAmp) {
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
                Some(JavaTokKind::EqEq) => Some(BinOp::Eq),
                Some(JavaTokKind::BangEq) => Some(BinOp::Ne),
                Some(JavaTokKind::Lt) => Some(BinOp::Lt),
                Some(JavaTokKind::Le) => Some(BinOp::Le),
                Some(JavaTokKind::Gt) => Some(BinOp::Gt),
                Some(JavaTokKind::Ge) => Some(BinOp::Ge),
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
                Some(JavaTokKind::Plus) => Some(BinOp::Add),
                Some(JavaTokKind::Minus) => Some(BinOp::Sub),
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
                Some(JavaTokKind::Star) => Some(BinOp::Mul),
                Some(JavaTokKind::Slash) => Some(BinOp::Div),
                Some(JavaTokKind::Percent) => Some(BinOp::Mod),
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
        if self.eat(&JavaTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        if self.eat(&JavaTokKind::Bang) {
            // `!Objects.equals(a, b)` -> `BinOp::Ne(a, b)`
            if matches!(self.peek_kind(), Some(JavaTokKind::Ident(s)) if s == "Objects")
                && matches!(self.peek_kind_at(1), Some(JavaTokKind::Dot))
                && matches!(self.peek_kind_at(2), Some(JavaTokKind::Ident(m)) if m == "equals")
                && matches!(self.peek_kind_at(3), Some(JavaTokKind::LParen))
            {
                self.pos += 4;
                let a = self.parse_expr()?;
                self.expect(&JavaTokKind::Comma, "','")?;
                let b = self.parse_expr()?;
                self.expect(&JavaTokKind::RParen, "')'")?;
                return Ok(Expr::Binary {
                    op: BinOp::Ne,
                    left: Box::new(a),
                    right: Box::new(b),
                });
            }
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Not,
                expr: Box::new(inner),
            });
        }
        // Unwrap Java primitive casts `(int) x` / `(long) x` / `(double) x`
        if matches!(self.peek_kind(), Some(JavaTokKind::LParen))
            && matches!(
                self.peek_kind_at(1),
                Some(JavaTokKind::Ident(t)) if matches!(t.as_str(), "int" | "long" | "double")
            )
            && matches!(self.peek_kind_at(2), Some(JavaTokKind::RParen))
        {
            self.pos += 3;
            return self.parse_unary();
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut base = self.parse_primary()?;
        loop {
            if self.eat(&JavaTokKind::Dot) {
                let member = self.expect_ident()?;
                // Handle `System.out.println(...)`
                if let Expr::Var(ref ns) = base {
                    if ns == "System" && member == "out" {
                        self.expect(&JavaTokKind::Dot, "'.'")?;
                        let pm = self.expect_ident()?;
                        if pm != "println" && pm != "print" {
                            return self.err("expected println/print after System.out");
                        }
                        self.expect(&JavaTokKind::LParen, "'('")?;
                        let args = self.parse_println_args()?;
                        base = Expr::intrinsic(Intrinsic::Print(args));
                        continue;
                    }
                }

                if self.eat(&JavaTokKind::LParen) {
                    let mut args = self.parse_expr_list(&JavaTokKind::RParen)?;
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
                        (Expr::Var(ns), "valueOf", 1) if ns == "String" => {
                            Expr::intrinsic(Intrinsic::ToStr(args.pop().unwrap()))
                        }
                        (Expr::Var(ns), "equals", 2) if ns == "Objects" => {
                            let b = args.pop().unwrap();
                            let a = args.pop().unwrap();
                            Expr::Binary {
                                op: BinOp::Eq,
                                left: Box::new(a),
                                right: Box::new(b),
                            }
                        }
                        (Expr::Var(ns), "asList" | "of", _) if ns == "Arrays" || ns == "List" => {
                            Expr::List(args)
                        }
                        (Expr::Var(ns), "emptyList", 0) if ns == "Collections" => {
                            Expr::List(Vec::new())
                        }
                        (_, "size" | "length", 0) => Expr::intrinsic(Intrinsic::Len(base)),
                        (_, "add", 1) => Expr::intrinsic(Intrinsic::Push {
                            list: base,
                            value: args.pop().unwrap(),
                        }),
                        (_, "get", 1) => Expr::Index {
                            base: Box::new(base),
                            index: Box::new(args.pop().unwrap()),
                        },
                        (_, "contains", 1) => Expr::intrinsic(Intrinsic::Contains {
                            haystack: base,
                            needle: args.pop().unwrap(),
                        }),
                        (_, "toUpperCase", 0) => Expr::intrinsic(Intrinsic::Upper(base)),
                        (_, "toLowerCase", 0) => Expr::intrinsic(Intrinsic::Lower(base)),
                        // Support Java record field accessor `stats.count()` when `base` is not a list/str method
                        (_, fname, 0) => Expr::FieldAccess {
                            base: Box::new(base),
                            field: fname.to_string(),
                        },
                        _ => {
                            return self
                                .err(format!("unsupported Java method '.{}(...)'", member))
                        }
                    };
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
            } else {
                break;
            }
        }
        Ok(base)
    }

    fn parse_println_args(&mut self) -> Result<Vec<Expr>, Diagnostic> {
        if self.eat(&JavaTokKind::RParen) {
            return Ok(Vec::new());
        }
        // Detect `String.join(" ", String.valueOf(e1), String.valueOf(e2), ...)`
        if matches!(self.peek_kind(), Some(JavaTokKind::Ident(s)) if s == "String")
            && matches!(self.peek_kind_at(1), Some(JavaTokKind::Dot))
            && matches!(self.peek_kind_at(2), Some(JavaTokKind::Ident(m)) if m == "join")
            && matches!(self.peek_kind_at(3), Some(JavaTokKind::LParen))
        {
            self.pos += 4;
            let _sep = self.parse_expr()?;
            self.expect(&JavaTokKind::Comma, "','")?;
            let raw_args = self.parse_expr_list(&JavaTokKind::RParen)?;
            self.expect(&JavaTokKind::RParen, "')'")?;
            let unwrapped = raw_args
                .into_iter()
                .map(|e| match e {
                    Expr::Intrinsic(intr) => match *intr {
                        Intrinsic::ToStr(inner) => inner,
                        other => Expr::Intrinsic(Box::new(other)),
                    },
                    other => other,
                })
                .collect();
            return Ok(unwrapped);
        }

        let single = self.parse_expr()?;
        self.expect(&JavaTokKind::RParen, "')'")?;
        Ok(vec![single])
    }

    fn parse_primary(&mut self) -> Result<Expr, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(JavaTokKind::Int(v)) => {
                self.next();
                Ok(Expr::Int(v))
            }
            Some(JavaTokKind::Float(v)) => {
                self.next();
                Ok(Expr::Float(v))
            }
            Some(JavaTokKind::Str(s)) => {
                self.next();
                Ok(Expr::Str(s))
            }
            Some(JavaTokKind::LParen) => {
                self.next();
                let e = self.parse_expr()?;
                self.expect(&JavaTokKind::RParen, "')'")?;
                Ok(e)
            }
            Some(JavaTokKind::Ident(ident)) if ident == "new" => {
                self.next();
                let cname = self.expect_ident()?;
                // Optional generic diamond `<>` or `<Long>`
                if self.eat(&JavaTokKind::Lt) {
                    let mut depth = 1usize;
                    while depth > 0 {
                        match self.next().map(|t| t.kind) {
                            Some(JavaTokKind::Lt) => depth += 1,
                            Some(JavaTokKind::Gt) => depth -= 1,
                            Some(_) => {}
                            None => return self.err("unclosed '<' in generic constructor"),
                        }
                    }
                }
                self.expect(&JavaTokKind::LParen, "'('")?;
                let mut args = self.parse_expr_list(&JavaTokKind::RParen)?;
                if cname == "ArrayList" {
                    if args.is_empty() {
                        return Ok(Expr::List(Vec::new()));
                    }
                    if args.len() == 1 {
                        if let Expr::List(items) = args.pop().unwrap() {
                            return Ok(Expr::List(items));
                        }
                    }
                    return Ok(Expr::List(args));
                }

                let field_names = self
                    .struct_field_order
                    .get(&cname)
                    .cloned()
                    .unwrap_or_default();
                let fields: Vec<(String, Expr)> = args
                    .into_iter()
                    .enumerate()
                    .map(|(idx, val)| {
                        let fname = field_names
                            .get(idx)
                            .cloned()
                            .unwrap_or_else(|| format!("field_{}", idx));
                        (fname, val)
                    })
                    .collect();
                Ok(Expr::StructInit {
                    name: cname,
                    fields,
                })
            }
            Some(JavaTokKind::Ident(ident)) => {
                self.next();
                if ident == "true" {
                    return Ok(Expr::Bool(true));
                }
                if ident == "false" {
                    return Ok(Expr::Bool(false));
                }
                if self.eat(&JavaTokKind::LParen) {
                    let args = self.parse_expr_list(&JavaTokKind::RParen)?;
                    return Ok(Expr::Call { func: ident, args });
                }
                Ok(Expr::Var(ident))
            }
            _ => self.err("expected Java expression"),
        }
    }

    fn parse_expr_list(&mut self, closing: &JavaTokKind) -> Result<Vec<Expr>, Diagnostic> {
        let mut items = Vec::new();
        while self.peek_kind() != Some(closing) && self.peek_kind().is_some() {
            items.push(self.parse_expr()?);
            if !self.eat(&JavaTokKind::Comma) {
                break;
            }
        }
        self.expect(closing, "closing delimiter")?;
        Ok(items)
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
        _ => None,
    }
}

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl,
    HubModule, Intrinsic, Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl,
    Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct CLens;

impl LanguageLens for CLens {
    fn id(&self) -> SpokeId {
        SpokeId::C
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut ctx = CFmtCtx::from_hub(hub);
        let usage = ctx.scan_usage(hub);
        let mut out = String::new();
        ctx.emit_full_module(hub, &usage, &mut out);
        out
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_c(source)?;
        let mut known_enums: HashSet<String> = HashSet::new();
        let mut struct_fields: HashMap<String, Vec<(String, Type)>> = HashMap::new();
        for item in &prev_hub.items {
            match item {
                Item::Enum(e) => {
                    known_enums.insert(e.name.clone());
                }
                Item::Struct(s) => {
                    struct_fields.insert(
                        s.name.clone(),
                        s.fields
                            .iter()
                            .map(|f| (f.name.clone(), f.ty.clone()))
                            .collect(),
                    );
                }
                _ => {}
            }
        }
        prescan_c_types(&tokens, &mut known_enums, &mut struct_fields);

        let mut parser = CParser {
            tokens,
            pos: 0,
            known_enums,
            struct_fields,
            local_types: HashMap::new(),
            param_types: HashMap::new(),
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::C))
    }
}

struct CUsage {
    headers: BTreeSet<&'static str>,
    need_str_eq: bool,
    need_str_concat: bool,
    need_str_contains: bool,
    need_upper: bool,
    need_lower: bool,
    need_int_to_str: bool,
    need_float_to_str: bool,
    need_fmt_f64: bool,
    need_bool_to_str: bool,
    need_str_id: bool,
    need_min_i64: bool,
    need_max_i64: bool,
    need_abs_i64: bool,
    prim_lists: Vec<Type>,
    named_lists: HashMap<String, Vec<Type>>,
    need_forward_protos: bool,
}

struct CFmtCtx {
    fn_ret_types: HashMap<String, Type>,
    struct_fields: HashMap<String, HashMap<String, Type>>,
    enum_names: HashSet<String>,
    local_env: HashMap<String, Type>,
    loop_counter: usize,
}

impl CFmtCtx {
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
            loop_counter: 0,
        }
    }

    fn emit_full_module(&mut self, hub: &HubModule, usage: &CUsage, out: &mut String) {
        for h in &usage.headers {
            out.push_str(&format!("#include <{}>\n", h));
        }

        let mut rt = String::new();
        if usage.need_str_eq {
            rt.push_str(
                "static inline bool star_str_eq(const char* a, const char* b) { return strcmp(a, b) == 0; }\n",
            );
            rt.push_str(
                "static inline bool star_str_ne(const char* a, const char* b) { return strcmp(a, b) != 0; }\n",
            );
        }
        if usage.need_str_concat {
            rt.push_str(
                "static inline const char* star_str_concat(const char* a, const char* b) {\n    size_t la = strlen(a), lb = strlen(b);\n    char* buf = (char*)malloc(la + lb + 1);\n    memcpy(buf, a, la);\n    memcpy(buf + la, b, lb + 1);\n    return buf;\n}\n",
            );
        }
        if usage.need_str_contains {
            rt.push_str(
                "static inline bool star_str_contains(const char* h, const char* n) { return strstr(h, n) != NULL; }\n",
            );
        }
        if usage.need_upper {
            rt.push_str(
                "static inline const char* star_str_upper(const char* s) {\n    size_t n = strlen(s);\n    char* buf = (char*)malloc(n + 1);\n    for (size_t i = 0; i <= n; i++) buf[i] = (char)toupper((unsigned char)s[i]);\n    return buf;\n}\n",
            );
        }
        if usage.need_lower {
            rt.push_str(
                "static inline const char* star_str_lower(const char* s) {\n    size_t n = strlen(s);\n    char* buf = (char*)malloc(n + 1);\n    for (size_t i = 0; i <= n; i++) buf[i] = (char)tolower((unsigned char)s[i]);\n    return buf;\n}\n",
            );
        }
        if usage.need_int_to_str {
            rt.push_str(
                "static inline const char* star_int_to_str(int64_t v) {\n    char* buf = (char*)malloc(32);\n    snprintf(buf, 32, \"%lld\", (long long)v);\n    return buf;\n}\n",
            );
        }
        if usage.need_float_to_str {
            rt.push_str(
                "static inline const char* star_float_to_str(double v) {\n    char* buf = (char*)malloc(64);\n    snprintf(buf, 64, \"%.15g\", v);\n    return buf;\n}\n",
            );
        }
        if usage.need_fmt_f64 {
            rt.push_str(
                "static inline const char* star_fmt_f64(double v) {\n    char* buf = (char*)malloc(64);\n    snprintf(buf, 64, \"%.15g\", v);\n    return buf;\n}\n",
            );
        }
        if usage.need_bool_to_str {
            rt.push_str(
                "static inline const char* star_bool_to_str(bool v) { return v ? \"true\" : \"false\"; }\n",
            );
        }
        if usage.need_str_id {
            rt.push_str("static inline const char* star_str_id(const char* s) { return s; }\n");
        }
        if usage.need_min_i64 {
            rt.push_str(
                "static inline int64_t star_min_i64(int64_t a, int64_t b) { return a < b ? a : b; }\n",
            );
        }
        if usage.need_max_i64 {
            rt.push_str(
                "static inline int64_t star_max_i64(int64_t a, int64_t b) { return a > b ? a : b; }\n",
            );
        }
        if usage.need_abs_i64 {
            rt.push_str(
                "static inline int64_t star_abs_i64(int64_t a) { return a < 0 ? -a : a; }\n",
            );
        }

        for elem_ty in &usage.prim_lists {
            self.fmt_list_runtime(elem_ty, &mut rt);
        }

        if !rt.is_empty() {
            out.push('\n');
            out.push_str(&rt);
        }

        let mut protos_emitted = false;
        for item in &hub.items {
            if matches!(item, Item::Function(_) | Item::Test(_))
                && usage.need_forward_protos
                && !protos_emitted
            {
                out.push('\n');
                for fn_item in &hub.items {
                    if let Item::Function(f) = fn_item {
                        if f.name != "main" {
                            let params_str = if f.params.is_empty() {
                                "void".to_string()
                            } else {
                                f.params
                                    .iter()
                                    .map(|p| format!("{} {}", Self::fmt_type(&p.ty), p.name))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            };
                            out.push_str(&format!(
                                "{} {}({});\n",
                                Self::fmt_type(&f.ret_ty),
                                f.name,
                                params_str
                            ));
                        }
                    }
                }
                protos_emitted = true;
            }

            out.push('\n');
            match item {
                Item::Enum(e) => {
                    self.fmt_enum(e, out);
                    if let Some(dep_lists) = usage.named_lists.get(&e.name) {
                        for elem_ty in dep_lists {
                            self.fmt_list_runtime(elem_ty, out);
                        }
                    }
                }
                Item::Struct(s) => {
                    self.fmt_struct(s, out);
                    if let Some(dep_lists) = usage.named_lists.get(&s.name) {
                        for elem_ty in dep_lists {
                            self.fmt_list_runtime(elem_ty, out);
                        }
                    }
                }
                Item::Function(f) => self.fmt_fn(f, out),
                Item::Test(t) => self.fmt_test(t, out),
            }
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

    fn type_slug(ty: &Type) -> String {
        match ty {
            Type::Int => "int64_t".to_string(),
            Type::Float => "double".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Str => "str".to_string(),
            Type::Void => "void".to_string(),
            Type::Named(n) => n.clone(),
            Type::List(inner) => format!("StarList_{}", Self::type_slug(inner)),
        }
    }

    fn list_struct_name(elem_ty: &Type) -> String {
        format!("StarList_{}", Self::type_slug(elem_ty))
    }

    fn fmt_type(ty: &Type) -> String {
        match ty {
            Type::Int => "int64_t".to_string(),
            Type::Float => "double".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Str => "const char*".to_string(),
            Type::Void => "void".to_string(),
            Type::Named(n) => n.clone(),
            Type::List(inner) => Self::list_struct_name(inner),
        }
    }

    fn fmt_decl_type(ty: &Type, is_const: bool) -> String {
        if *ty == Type::Str {
            if is_const {
                "const char* const".to_string()
            } else {
                "const char*".to_string()
            }
        } else if is_const {
            format!("const {}", Self::fmt_type(ty))
        } else {
            Self::fmt_type(ty)
        }
    }

    fn leaf_named_type(ty: &Type) -> Option<String> {
        match ty {
            Type::Named(n) => Some(n.clone()),
            Type::List(inner) => Self::leaf_named_type(inner),
            _ => None,
        }
    }

    fn type_nesting_depth(ty: &Type) -> usize {
        match ty {
            Type::List(inner) => 1 + Self::type_nesting_depth(inner),
            _ => 0,
        }
    }

    fn fmt_eq_call(&self, ty: &Type, a: &str, b: &str) -> String {
        match ty {
            Type::Str => format!("star_str_eq({}, {})", a, b),
            Type::List(inner) => format!("{}_eq({}, {})", Self::list_struct_name(inner), a, b),
            Type::Named(n) if !self.enum_names.contains(n) => format!("{}_eq({}, {})", n, a, b),
            _ => format!("({} == {})", a, b),
        }
    }

    fn fmt_list_runtime(&self, elem_ty: &Type, out: &mut String) {
        let lname = Self::list_struct_name(elem_ty);
        let elem_c = Self::fmt_type(elem_ty);
        let eq_contain = self.fmt_eq_call(elem_ty, "l.data[i]", "v");
        let eq_pair = self.fmt_eq_call(elem_ty, "a.data[i]", "b.data[i]");
        out.push_str(&format!(
            "typedef struct {ln} {{ {ec}* data; int64_t len; int64_t cap; }} {ln};\n",
            ln = lname,
            ec = elem_c
        ));
        out.push_str(&format!(
            "static inline {ln} {ln}_of(const {ec}* src, int64_t n) {{ {ln} o = {{ NULL, n, n }}; if (n > 0) {{ o.data = ({ec}*)malloc((size_t)n * sizeof({ec})); memcpy(o.data, src, (size_t)n * sizeof({ec})); }} return o; }}\n",
            ln = lname,
            ec = elem_c
        ));
        out.push_str(&format!(
            "static inline void {ln}_push({ln}* l, {ec} v) {{ if (l->len >= l->cap) {{ int64_t nc = l->cap == 0 ? 4 : l->cap * 2; {ec}* nd = ({ec}*)malloc((size_t)nc * sizeof({ec})); if (l->len > 0) memcpy(nd, l->data, (size_t)l->len * sizeof({ec})); l->data = nd; l->cap = nc; }} l->data[l->len++] = v; }}\n",
            ln = lname,
            ec = elem_c
        ));
        out.push_str(&format!(
            "static inline bool {ln}_contains({ln} l, {ec} v) {{ for (int64_t i = 0; i < l.len; i++) {{ if ({eq_c}) return true; }} return false; }}\n",
            ln = lname,
            ec = elem_c,
            eq_c = eq_contain
        ));
        out.push_str(&format!(
            "static inline bool {ln}_eq({ln} a, {ln} b) {{ if (a.len != b.len) return false; for (int64_t i = 0; i < a.len; i++) {{ if (!{eq_p}) return false; }} return true; }}\n",
            ln = lname,
            eq_p = eq_pair
        ));
        out.push_str(&format!(
            "static inline bool {ln}_ne({ln} a, {ln} b) {{ return !{ln}_eq(a, b); }}\n",
            ln = lname
        ));
    }

    fn scan_usage(&mut self, hub: &HubModule) -> CUsage {
        let mut usage = CUsage {
            headers: BTreeSet::new(),
            need_str_eq: false,
            need_str_concat: false,
            need_str_contains: false,
            need_upper: false,
            need_lower: false,
            need_int_to_str: false,
            need_float_to_str: false,
            need_fmt_f64: false,
            need_bool_to_str: false,
            need_str_id: false,
            need_min_i64: false,
            need_max_i64: false,
            need_abs_i64: false,
            prim_lists: Vec::new(),
            named_lists: HashMap::new(),
            need_forward_protos: false,
        };
        usage.headers.insert("stdbool.h");
        usage.headers.insert("stdint.h");
        usage.headers.insert("stdio.h");

        let mut list_elems: Vec<Type> = Vec::new();
        fn record_list_ty(ty: &Type, list_elems: &mut Vec<Type>) {
            if let Type::List(inner) = ty {
                record_list_ty(inner, list_elems);
                if !list_elems.contains(inner) {
                    list_elems.push((**inner).clone());
                }
            }
        }

        let mut defined_fns: HashSet<String> = HashSet::new();

        for item in &hub.items {
            match item {
                Item::Struct(s) => {
                    for f in &s.fields {
                        record_list_ty(&f.ty, &mut list_elems);
                        if f.ty == Type::Str {
                            usage.need_str_eq = true;
                            usage.headers.insert("string.h");
                        }
                    }
                }
                Item::Enum(_) => {}
                Item::Function(f) => {
                    self.local_env.clear();
                    for p in &f.params {
                        record_list_ty(&p.ty, &mut list_elems);
                        self.local_env.insert(p.name.clone(), p.ty.clone());
                    }
                    record_list_ty(&f.ret_ty, &mut list_elems);
                    self.scan_stmts(&f.body, &mut usage, &mut list_elems, &defined_fns, &f.name);
                    defined_fns.insert(f.name.clone());
                }
                Item::Test(t) => {
                    self.local_env.clear();
                    self.scan_stmts(&t.body, &mut usage, &mut list_elems, &defined_fns, "");
                }
            }
        }

        if !list_elems.is_empty() {
            usage.headers.insert("stdlib.h");
            usage.headers.insert("string.h");
            for el in &list_elems {
                if Self::contains_str_ty(el) {
                    usage.need_str_eq = true;
                }
            }
        }

        list_elems.sort_by_key(Self::type_nesting_depth);
        for el in list_elems {
            if let Some(leaf_name) = Self::leaf_named_type(&el) {
                usage.named_lists.entry(leaf_name).or_default().push(el);
            } else {
                usage.prim_lists.push(el);
            }
        }

        usage
    }

    fn contains_str_ty(ty: &Type) -> bool {
        match ty {
            Type::Str => true,
            Type::List(inner) => Self::contains_str_ty(inner),
            _ => false,
        }
    }

    fn scan_stmts(
        &mut self,
        stmts: &[Stmt],
        usage: &mut CUsage,
        list_elems: &mut Vec<Type>,
        defined_fns: &HashSet<String>,
        current_fn: &str,
    ) {
        fn add_list(ty: &Type, list_elems: &mut Vec<Type>) {
            if let Type::List(inner) = ty {
                add_list(inner, list_elems);
                if !list_elems.contains(inner) {
                    list_elems.push((**inner).clone());
                }
            }
        }

        for stmt in stmts {
            match stmt {
                Stmt::Let {
                    name, ty, value, ..
                } => {
                    self.scan_expr(value, usage, list_elems, defined_fns, current_fn);
                    let resolved = ty.clone().or_else(|| self.expr_ty(value));
                    if let Some(t) = resolved {
                        add_list(&t, list_elems);
                        self.local_env.insert(name.clone(), t);
                    }
                }
                Stmt::Assign { target, value, .. } => {
                    if let AssignTarget::Index { index, .. } = target {
                        self.scan_expr(index, usage, list_elems, defined_fns, current_fn);
                    }
                    self.scan_expr(value, usage, list_elems, defined_fns, current_fn);
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    self.scan_expr(cond, usage, list_elems, defined_fns, current_fn);
                    let saved = self.local_env.clone();
                    self.scan_stmts(then_body, usage, list_elems, defined_fns, current_fn);
                    self.local_env = saved.clone();
                    self.scan_stmts(else_body, usage, list_elems, defined_fns, current_fn);
                    self.local_env = saved;
                }
                Stmt::Match { expr, arms, .. } => {
                    self.scan_expr(expr, usage, list_elems, defined_fns, current_fn);
                    if self.expr_ty(expr) == Some(Type::Str)
                        || arms.iter().any(|a| matches!(a.pat, MatchPat::Str(_)))
                    {
                        usage.need_str_eq = true;
                        usage.headers.insert("string.h");
                    }
                    for arm in arms {
                        let saved = self.local_env.clone();
                        self.scan_stmts(&arm.body, usage, list_elems, defined_fns, current_fn);
                        self.local_env = saved;
                    }
                }
                Stmt::While { cond, body, .. } => {
                    self.scan_expr(cond, usage, list_elems, defined_fns, current_fn);
                    let saved = self.local_env.clone();
                    self.scan_stmts(body, usage, list_elems, defined_fns, current_fn);
                    self.local_env = saved;
                }
                Stmt::ForEach {
                    var, iter, body, ..
                } => {
                    self.scan_expr(iter, usage, list_elems, defined_fns, current_fn);
                    let saved = self.local_env.clone();
                    if let Some(it_ty) = self.expr_ty(iter) {
                        add_list(&it_ty, list_elems);
                        if let Type::List(elem) = it_ty {
                            self.local_env.insert(var.clone(), *elem);
                        }
                    }
                    self.scan_stmts(body, usage, list_elems, defined_fns, current_fn);
                    self.local_env = saved;
                }
                Stmt::ForRange {
                    var,
                    start,
                    end,
                    body,
                    ..
                } => {
                    self.scan_expr(start, usage, list_elems, defined_fns, current_fn);
                    self.scan_expr(end, usage, list_elems, defined_fns, current_fn);
                    let saved = self.local_env.clone();
                    self.local_env.insert(var.clone(), Type::Int);
                    self.scan_stmts(body, usage, list_elems, defined_fns, current_fn);
                    self.local_env = saved;
                }
                Stmt::Return {
                    value: Some(v), ..
                } => {
                    self.scan_expr(v, usage, list_elems, defined_fns, current_fn);
                }
                Stmt::Assert { cond, .. } => {
                    usage.headers.insert("assert.h");
                    self.scan_expr(cond, usage, list_elems, defined_fns, current_fn);
                }
                Stmt::AssertEq { left, right, .. } => {
                    usage.headers.insert("assert.h");
                    let eq = Expr::Binary {
                        op: BinOp::Eq,
                        left: Box::new(left.clone()),
                        right: Box::new(right.clone()),
                    };
                    self.scan_expr(&eq, usage, list_elems, defined_fns, current_fn);
                }
                Stmt::Expr { expr, .. } => {
                    self.scan_expr(expr, usage, list_elems, defined_fns, current_fn);
                }
                _ => {}
            }
        }
    }

    fn scan_expr(
        &self,
        expr: &Expr,
        usage: &mut CUsage,
        list_elems: &mut Vec<Type>,
        defined_fns: &HashSet<String>,
        current_fn: &str,
    ) {
        match expr {
            Expr::List(items) => {
                let elem_ty = items
                    .first()
                    .and_then(|e| self.expr_ty(e))
                    .unwrap_or(Type::Int);
                if !list_elems.contains(&elem_ty) {
                    list_elems.push(elem_ty);
                }
                for it in items {
                    self.scan_expr(it, usage, list_elems, defined_fns, current_fn);
                }
            }
            Expr::StructInit { fields, .. } => {
                for (_, v) in fields {
                    self.scan_expr(v, usage, list_elems, defined_fns, current_fn);
                }
            }
            Expr::FieldAccess { base, .. } | Expr::Unary { expr: base, .. } => {
                self.scan_expr(base, usage, list_elems, defined_fns, current_fn);
            }
            Expr::Index { base, index } => {
                self.scan_expr(base, usage, list_elems, defined_fns, current_fn);
                self.scan_expr(index, usage, list_elems, defined_fns, current_fn);
            }
            Expr::Binary { op, left, right } => {
                self.scan_expr(left, usage, list_elems, defined_fns, current_fn);
                self.scan_expr(right, usage, list_elems, defined_fns, current_fn);
                let lty = self.expr_ty(left);
                let rty = self.expr_ty(right);
                if *op == BinOp::Add && (lty == Some(Type::Str) || rty == Some(Type::Str)) {
                    usage.need_str_concat = true;
                    usage.headers.insert("stdlib.h");
                    usage.headers.insert("string.h");
                }
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    let cmp_ty = lty.or(rty);
                    if cmp_ty == Some(Type::Str) {
                        usage.need_str_eq = true;
                        usage.headers.insert("string.h");
                    } else if let Some(Type::List(inner)) = cmp_ty {
                        if !list_elems.contains(&inner) {
                            list_elems.push(*inner);
                        }
                    }
                }
            }
            Expr::Call { func, args } => {
                if !defined_fns.contains(func) && func != current_fn && self.fn_ret_types.contains_key(func) {
                    usage.need_forward_protos = true;
                }
                for a in args {
                    self.scan_expr(a, usage, list_elems, defined_fns, current_fn);
                }
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e) => {
                    self.scan_expr(e, usage, list_elems, defined_fns, current_fn);
                    if self.expr_ty(e) == Some(Type::Str) {
                        usage.headers.insert("string.h");
                    }
                }
                Intrinsic::Min(a, b) => {
                    self.scan_expr(a, usage, list_elems, defined_fns, current_fn);
                    self.scan_expr(b, usage, list_elems, defined_fns, current_fn);
                    if self.expr_ty(a) == Some(Type::Float) || self.expr_ty(b) == Some(Type::Float)
                    {
                        usage.headers.insert("math.h");
                    } else {
                        usage.need_min_i64 = true;
                    }
                }
                Intrinsic::Max(a, b) => {
                    self.scan_expr(a, usage, list_elems, defined_fns, current_fn);
                    self.scan_expr(b, usage, list_elems, defined_fns, current_fn);
                    if self.expr_ty(a) == Some(Type::Float) || self.expr_ty(b) == Some(Type::Float)
                    {
                        usage.headers.insert("math.h");
                    } else {
                        usage.need_max_i64 = true;
                    }
                }
                Intrinsic::Abs(a) => {
                    self.scan_expr(a, usage, list_elems, defined_fns, current_fn);
                    if self.expr_ty(a) == Some(Type::Float) {
                        usage.headers.insert("math.h");
                    } else {
                        usage.need_abs_i64 = true;
                    }
                }
                Intrinsic::Push { list, value } => {
                    self.scan_expr(list, usage, list_elems, defined_fns, current_fn);
                    self.scan_expr(value, usage, list_elems, defined_fns, current_fn);
                    if let Some(Type::List(inner)) = self.expr_ty(list) {
                        if !list_elems.contains(&inner) {
                            list_elems.push(*inner);
                        }
                    }
                }
                Intrinsic::Print(args) => {
                    for a in args {
                        self.scan_expr(a, usage, list_elems, defined_fns, current_fn);
                        if self.expr_ty(a) == Some(Type::Float) {
                            usage.need_fmt_f64 = true;
                            usage.headers.insert("stdlib.h");
                        }
                    }
                }
                Intrinsic::Contains { haystack, needle } => {
                    self.scan_expr(haystack, usage, list_elems, defined_fns, current_fn);
                    self.scan_expr(needle, usage, list_elems, defined_fns, current_fn);
                    if self.expr_ty(haystack) == Some(Type::Str) {
                        usage.need_str_contains = true;
                        usage.headers.insert("string.h");
                    } else if let Some(Type::List(inner)) = self.expr_ty(haystack) {
                        if !list_elems.contains(&inner) {
                            list_elems.push(*inner);
                        }
                    }
                }
                Intrinsic::Upper(e) => {
                    self.scan_expr(e, usage, list_elems, defined_fns, current_fn);
                    usage.need_upper = true;
                    usage.headers.insert("ctype.h");
                    usage.headers.insert("stdlib.h");
                    usage.headers.insert("string.h");
                }
                Intrinsic::Lower(e) => {
                    self.scan_expr(e, usage, list_elems, defined_fns, current_fn);
                    usage.need_lower = true;
                    usage.headers.insert("ctype.h");
                    usage.headers.insert("stdlib.h");
                    usage.headers.insert("string.h");
                }
                Intrinsic::ToStr(e) => {
                    self.scan_expr(e, usage, list_elems, defined_fns, current_fn);
                    match self.expr_ty(e) {
                        Some(Type::Float) => {
                            usage.need_float_to_str = true;
                            usage.headers.insert("stdlib.h");
                        }
                        Some(Type::Bool) => {
                            usage.need_bool_to_str = true;
                        }
                        Some(Type::Str) => {
                            usage.need_str_id = true;
                        }
                        _ => {
                            usage.need_int_to_str = true;
                            usage.headers.insert("stdlib.h");
                        }
                    }
                }
            },
            _ => {}
        }
    }

    fn fmt_enum(&self, e: &EnumDecl, out: &mut String) {
        for c in &e.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("typedef enum {} {{\n", e.name));
        for (idx, v) in e.variants.iter().enumerate() {
            out.push_str(&format!("    {}_{} = {},\n", e.name, v, idx));
        }
        out.push_str(&format!("}} {};\n", e.name));
    }

    fn fmt_struct(&self, s: &StructDecl, out: &mut String) {
        for c in &s.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("typedef struct {} {{\n", s.name));
        if s.fields.is_empty() {
            out.push_str("    uint8_t _empty;\n");
        } else {
            for f in &s.fields {
                out.push_str(&format!("    {} {};\n", Self::fmt_type(&f.ty), f.name));
            }
        }
        out.push_str(&format!("}} {};\n", s.name));

        let eq_body = if s.fields.is_empty() {
            "(void)a; (void)b; return true;".to_string()
        } else {
            let parts: Vec<String> = s
                .fields
                .iter()
                .map(|f| {
                    let fa = format!("a.{}", f.name);
                    let fb = format!("b.{}", f.name);
                    self.fmt_eq_call(&f.ty, &fa, &fb)
                })
                .collect();
            format!("return {};", parts.join(" && "))
        };
        out.push_str(&format!(
            "static inline bool {n}_eq({n} a, {n} b) {{ {body} }}\n",
            n = s.name,
            body = eq_body
        ));
        out.push_str(&format!(
            "static inline bool {n}_ne({n} a, {n} b) {{ return !{n}_eq(a, b); }}\n",
            n = s.name
        ));
    }

    fn fmt_fn(&mut self, f: &FnDecl, out: &mut String) {
        for c in &f.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        self.loop_counter = 0;
        for p in &f.params {
            self.local_env.insert(p.name.clone(), p.ty.clone());
        }

        let params_str = if f.params.is_empty() {
            "void".to_string()
        } else {
            f.params
                .iter()
                .map(|p| format!("{} {}", Self::fmt_type(&p.ty), p.name))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let ret_str = if f.name == "main" && f.ret_ty == Type::Void {
            "int".to_string()
        } else {
            Self::fmt_type(&f.ret_ty)
        };

        out.push_str(&format!("{} {}({}) {{\n", ret_str, f.name, params_str));
        for s in &f.body {
            self.fmt_stmt(s, 1, out);
        }
        if f.name == "main" && f.ret_ty == Type::Void {
            out.push_str("    return 0;\n");
        } else if f.ret_ty != Type::Void && !c_block_terminates(&f.body) {
            out.push_str("    __builtin_unreachable();\n");
        }
        out.push_str("}\n");
    }

    fn fmt_test(&mut self, t: &TestDecl, out: &mut String) {
        for c in &t.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        self.loop_counter = 0;
        out.push_str(&format!("void test_{}(void) {{\n", t.name));
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
                let resolved_ty = ty
                    .clone()
                    .or_else(|| self.expr_ty(value))
                    .unwrap_or(Type::Int);
                let val_str = match (&resolved_ty, value) {
                    (Type::List(_), Expr::List(items)) if items.is_empty() => "{0}".to_string(),
                    _ => self.fmt_expr(value),
                };
                let decl_ty = Self::fmt_decl_type(&resolved_ty, !*mutable);
                self.local_env.insert(name.clone(), resolved_ty);
                out.push_str(&format!("{}{} {} = {};\n", pad, decl_ty, name, val_str));
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
                        format!("{}.data[{}]", base, self.fmt_expr(index))
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
                            let cond_str =
                                format!("star_str_eq({}, {})", scrut, self.fmt_pat(&arm.pat));
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
                            Some(
                                Stmt::Return { .. } | Stmt::Break { .. } | Stmt::Continue { .. }
                            )
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
                let loop_id = self.loop_counter;
                self.loop_counter += 1;
                let idx_var = format!("_idx_{}", loop_id);
                let list_ty = self
                    .expr_ty(iter)
                    .unwrap_or_else(|| Type::list(Type::Int));
                let elem_ty = match &list_ty {
                    Type::List(inner) => (**inner).clone(),
                    _ => Type::Int,
                };
                let elem_decl = Self::fmt_decl_type(&elem_ty, true);

                let is_simple_iter = matches!(iter, Expr::Var(_) | Expr::FieldAccess { .. });
                if is_simple_iter {
                    let iter_s = self.fmt_postfix(iter);
                    out.push_str(&format!(
                        "{}for (int64_t {} = 0; {} < {}.len; {}++) {{\n",
                        pad, idx_var, idx_var, iter_s, idx_var
                    ));
                    out.push_str(&format!(
                        "{}    {} {} = {}.data[{}];\n",
                        pad, elem_decl, var, iter_s, idx_var
                    ));
                    let saved = self.local_env.clone();
                    self.local_env.insert(var.clone(), elem_ty);
                    for s in body {
                        self.fmt_stmt(s, indent + 1, out);
                    }
                    self.local_env = saved;
                    out.push_str(&format!("{}}}\n", pad));
                } else {
                    let iter_var = format!("_iter_{}", loop_id);
                    out.push_str(&format!("{}{{\n", pad));
                    out.push_str(&format!(
                        "{}    {} {} = {};\n",
                        pad,
                        Self::fmt_decl_type(&list_ty, true),
                        iter_var,
                        self.fmt_expr(iter)
                    ));
                    out.push_str(&format!(
                        "{}    for (int64_t {} = 0; {} < {}.len; {}++) {{\n",
                        pad, idx_var, idx_var, iter_var, idx_var
                    ));
                    out.push_str(&format!(
                        "{}        {} {} = {}.data[{}];\n",
                        pad, elem_decl, var, iter_var, idx_var
                    ));
                    let saved = self.local_env.clone();
                    self.local_env.insert(var.clone(), elem_ty);
                    for s in body {
                        self.fmt_stmt(s, indent + 2, out);
                    }
                    self.local_env = saved;
                    out.push_str(&format!("{}    }}\n", pad));
                    out.push_str(&format!("{}}}\n", pad));
                }
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
            Expr::Binary { .. } | Expr::Unary { .. } | Expr::StructInit { .. } => {
                format!("({})", s)
            }
            _ => s,
        }
    }

    fn fmt_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => {
                if *v > i32::MAX as i64 || *v < i32::MIN as i64 {
                    format!("{}LL", v)
                } else {
                    v.to_string()
                }
            }
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
                let lname = Self::list_struct_name(&elem_ty);
                if items.is_empty() {
                    format!("(({}){{0}})", lname)
                } else {
                    let elem_c = Self::fmt_type(&elem_ty);
                    let inner: Vec<String> = items.iter().map(|e| self.fmt_expr(e)).collect();
                    format!(
                        "{}_of((const {}[]){{{}}}, {})",
                        lname,
                        elem_c,
                        inner.join(", "),
                        items.len()
                    )
                }
            }
            Expr::StructInit { name, fields } => {
                if fields.is_empty() {
                    format!("({}){{ ._empty = 0 }}", name)
                } else {
                    let inner: Vec<String> = fields
                        .iter()
                        .map(|(fname, fval)| format!(".{} = {}", fname, self.fmt_expr(fval)))
                        .collect();
                    format!("({}){{ {} }}", name, inner.join(", "))
                }
            }
            Expr::FieldAccess { base, field } => format!("{}.{}", self.fmt_postfix(base), field),
            Expr::Index { base, index } => {
                format!("{}.data[{}]", self.fmt_postfix(base), self.fmt_expr(index))
            }
            Expr::Unary { op, expr: inner } => {
                if *op == UnaryOp::Neg {
                    if let Expr::Int(v) = inner.as_ref() {
                        if *v >= 2_147_483_648 {
                            return format!("-{}LL", v);
                        }
                        return format!("-{}", v);
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
                let lty = self.expr_ty(left);
                let rty = self.expr_ty(right);

                if *op == BinOp::Add && (lty == Some(Type::Str) || rty == Some(Type::Str)) {
                    return format!(
                        "star_str_concat({}, {})",
                        self.fmt_expr(left),
                        self.fmt_expr(right)
                    );
                }

                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    let cmp_ty = lty.clone().or(rty.clone());
                    let fmt_side = |side: &Expr, peer_ty: &Option<Type>| -> String {
                        if let Expr::List(items) = side {
                            if items.is_empty() {
                                if let Some(Type::List(elem)) = peer_ty {
                                    return format!("(({}){{0}})", Self::list_struct_name(elem));
                                }
                            }
                        }
                        self.fmt_expr(side)
                    };
                    let ls = fmt_side(left, &rty);
                    let rs = fmt_side(right, &lty);
                    match cmp_ty {
                        Some(Type::Str) => {
                            let fn_name = if *op == BinOp::Eq {
                                "star_str_eq"
                            } else {
                                "star_str_ne"
                            };
                            return format!("{}({}, {})", fn_name, ls, rs);
                        }
                        Some(Type::List(inner)) => {
                            let suf = if *op == BinOp::Eq { "eq" } else { "ne" };
                            return format!(
                                "{}_{}({}, {})",
                                Self::list_struct_name(&inner),
                                suf,
                                ls,
                                rs
                            );
                        }
                        Some(Type::Named(sname)) if !self.enum_names.contains(&sname) => {
                            let suf = if *op == BinOp::Eq { "eq" } else { "ne" };
                            return format!("{}_{}({}, {})", sname, suf, ls, rs);
                        }
                        _ => {}
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
                let inner: Vec<String> = args.iter().map(|a| self.fmt_expr(a)).collect();
                format!("{}({})", func, inner.join(", "))
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(e) => {
                    if self.expr_ty(e) == Some(Type::Str) {
                        format!("(int64_t)strlen({})", self.fmt_expr(e))
                    } else {
                        format!("{}.len", self.fmt_postfix(e))
                    }
                }
                Intrinsic::Min(a, b) => {
                    if self.expr_ty(a) == Some(Type::Float) || self.expr_ty(b) == Some(Type::Float)
                    {
                        format!("fmin({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                    } else {
                        format!("star_min_i64({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                    }
                }
                Intrinsic::Max(a, b) => {
                    if self.expr_ty(a) == Some(Type::Float) || self.expr_ty(b) == Some(Type::Float)
                    {
                        format!("fmax({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                    } else {
                        format!("star_max_i64({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                    }
                }
                Intrinsic::Abs(a) => {
                    if self.expr_ty(a) == Some(Type::Float) {
                        format!("fabs({})", self.fmt_expr(a))
                    } else {
                        format!("star_abs_i64({})", self.fmt_expr(a))
                    }
                }
                Intrinsic::Push { list, value } => {
                    let elem_ty = match self.expr_ty(list) {
                        Some(Type::List(inner)) => *inner,
                        _ => self.expr_ty(value).unwrap_or(Type::Int),
                    };
                    format!(
                        "{}_push(&{}, {})",
                        Self::list_struct_name(&elem_ty),
                        self.fmt_expr(list),
                        self.fmt_expr(value)
                    )
                }
                Intrinsic::Print(args) => {
                    if args.is_empty() {
                        return "printf(\"\\n\")".to_string();
                    }
                    let mut specs = Vec::with_capacity(args.len());
                    let mut c_args = Vec::with_capacity(args.len());
                    for a in args {
                        match self.expr_ty(a) {
                            Some(Type::Str) => {
                                specs.push("%s");
                                c_args.push(self.fmt_expr(a));
                            }
                            Some(Type::Bool) => {
                                specs.push("%s");
                                c_args.push(format!("(({}) ? \"true\" : \"false\")", self.fmt_expr(a)));
                            }
                            Some(Type::Float) => {
                                specs.push("%s");
                                c_args.push(format!("star_fmt_f64({})", self.fmt_expr(a)));
                            }
                            _ => {
                                specs.push("%lld");
                                c_args.push(format!("(long long)({})", self.fmt_expr(a)));
                            }
                        }
                    }
                    format!("printf(\"{}\\n\", {})", specs.join(" "), c_args.join(", "))
                }
                Intrinsic::Contains { haystack, needle } => {
                    if self.expr_ty(haystack) == Some(Type::Str) {
                        format!(
                            "star_str_contains({}, {})",
                            self.fmt_expr(haystack),
                            self.fmt_expr(needle)
                        )
                    } else {
                        let elem_ty = match self.expr_ty(haystack) {
                            Some(Type::List(inner)) => *inner,
                            _ => self.expr_ty(needle).unwrap_or(Type::Int),
                        };
                        format!(
                            "{}_contains({}, {})",
                            Self::list_struct_name(&elem_ty),
                            self.fmt_expr(haystack),
                            self.fmt_expr(needle)
                        )
                    }
                }
                Intrinsic::Upper(e) => format!("star_str_upper({})", self.fmt_expr(e)),
                Intrinsic::Lower(e) => format!("star_str_lower({})", self.fmt_expr(e)),
                Intrinsic::ToStr(e) => match self.expr_ty(e) {
                    Some(Type::Float) => format!("star_float_to_str({})", self.fmt_expr(e)),
                    Some(Type::Bool) => format!("star_bool_to_str({})", self.fmt_expr(e)),
                    Some(Type::Str) => format!("star_str_id({})", self.fmt_expr(e)),
                    _ => format!("star_int_to_str({})", self.fmt_expr(e)),
                },
            },
        }
    }
}

fn c_block_terminates(stmts: &[Stmt]) -> bool {
    let Some(last) = stmts.iter().rev().find(|s| !matches!(s, Stmt::Comment { .. })) else {
        return false;
    };
    match last {
        Stmt::Return { .. } => true,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => !else_body.is_empty() && c_block_terminates(then_body) && c_block_terminates(else_body),
        Stmt::Match { arms, .. } => {
            arms.iter().any(|a| a.pat == MatchPat::Wildcard)
                && arms.iter().all(|a| c_block_terminates(&a.body))
        }
        _ => false,
    }
}

// ============================================================================
// C11 Lexer & Recursive-Descent Parser (`put`)
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
    Question,
    Dot,
    Amp,
    Star,
    Plus,
    Minus,
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
    PlusPlus,
}

#[derive(Debug, Clone)]
struct CTok {
    kind: CTokKind,
    line: usize,
    col: usize,
}

fn lex_c(src: &str) -> Result<Vec<CTok>, Diagnostic> {
    let bytes = src.as_bytes();
    let n = bytes.len();
    let mut i = 0;
    let mut line = 1;
    let mut col = 1;
    let mut tokens = Vec::new();

    while i < n {
        let b = bytes[i];
        if b == b'\n' {
            i += 1;
            line += 1;
            col = 1;
            continue;
        }
        if b.is_ascii_whitespace() {
            i += 1;
            col += 1;
            continue;
        }

        // Preprocessor directives (`#include ...`, `#define ...`)
        if b == b'#' {
            while i < n && bytes[i] != b'\n' {
                if bytes[i] == b'\\' && i + 1 < n && bytes[i + 1] == b'\n' {
                    i += 2;
                    line += 1;
                    col = 1;
                    continue;
                }
                i += 1;
            }
            continue;
        }

        // Line comment `// ...`
        if b == b'/' && i + 1 < n && bytes[i + 1] == b'/' {
            let start_col = col;
            i += 2;
            col += 2;
            let start = i;
            while i < n && bytes[i] != b'\n' {
                i += 1;
                col += 1;
            }
            let text = src[start..i].trim().to_string();
            tokens.push(CTok {
                kind: CTokKind::Comment(text),
                line,
                col: start_col,
            });
            continue;
        }

        // Block comment `/* ... */`
        if b == b'/' && i + 1 < n && bytes[i + 1] == b'*' {
            let start_line = line;
            let start_col = col;
            i += 2;
            col += 2;
            while i + 1 < n && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                if bytes[i] == b'\n' {
                    line += 1;
                    col = 1;
                } else {
                    col += 1;
                }
                i += 1;
            }
            if i + 1 >= n {
                return Err(Diagnostic::new(
                    "c",
                    "unterminated block comment",
                    start_line,
                    start_col,
                ));
            }
            i += 2;
            col += 2;
            continue;
        }

        // String literal `"..."`
        if b == b'"' {
            let start_line = line;
            let start_col = col;
            i += 1;
            col += 1;
            let start = i;
            while i < n && bytes[i] != b'"' {
                if bytes[i] == b'\\' {
                    i += 2;
                    col += 2;
                    continue;
                }
                if bytes[i] == b'\n' {
                    return Err(Diagnostic::new(
                        "c",
                        "unterminated string literal",
                        start_line,
                        start_col,
                    ));
                }
                i += 1;
                col += 1;
            }
            if i >= n {
                return Err(Diagnostic::new(
                    "c",
                    "unterminated string literal",
                    start_line,
                    start_col,
                ));
            }
            let raw = &src[start..i];
            i += 1;
            col += 1;
            tokens.push(CTok {
                kind: CTokKind::Str(unescape_string(raw)),
                line: start_line,
                col: start_col,
            });
            continue;
        }

        // Number literal
        if b.is_ascii_digit() {
            let start_col = col;
            let start = i;
            let mut is_float = false;
            while i < n && bytes[i].is_ascii_digit() {
                i += 1;
                col += 1;
            }
            if i < n && bytes[i] == b'.' && i + 1 < n && bytes[i + 1].is_ascii_digit() {
                is_float = true;
                i += 1;
                col += 1;
                while i < n && bytes[i].is_ascii_digit() {
                    i += 1;
                    col += 1;
                }
            }
            if i < n && (bytes[i] == b'e' || bytes[i] == b'E') {
                is_float = true;
                i += 1;
                col += 1;
                if i < n && (bytes[i] == b'+' || bytes[i] == b'-') {
                    i += 1;
                    col += 1;
                }
                while i < n && bytes[i].is_ascii_digit() {
                    i += 1;
                    col += 1;
                }
            }
            let num_slice = &src[start..i];
            // Optional C integer/float suffixes (`L`, `LL`, `U`, `ULL`, `f`)
            while i < n && matches!(bytes[i], b'l' | b'L' | b'u' | b'U' | b'f' | b'F') {
                if bytes[i] == b'f' || bytes[i] == b'F' {
                    is_float = true;
                }
                i += 1;
                col += 1;
            }
            if is_float {
                let v = num_slice.parse::<f64>().map_err(|_| {
                    Diagnostic::new("c", format!("invalid float '{}'", num_slice), line, start_col)
                })?;
                tokens.push(CTok {
                    kind: CTokKind::Float(v),
                    line,
                    col: start_col,
                });
            } else {
                // Allow 2147483648..=9223372036854775807
                let v = num_slice.parse::<i64>().map_err(|_| {
                    Diagnostic::new(
                        "c",
                        format!("invalid integer '{}'", num_slice),
                        line,
                        start_col,
                    )
                })?;
                tokens.push(CTok {
                    kind: CTokKind::Int(v),
                    line,
                    col: start_col,
                });
            }
            continue;
        }

        // Identifier
        if b.is_ascii_alphabetic() || b == b'_' {
            let start_col = col;
            let start = i;
            while i < n && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
                col += 1;
            }
            tokens.push(CTok {
                kind: CTokKind::Ident(src[start..i].to_string()),
                line,
                col: start_col,
            });
            continue;
        }

        let start_col = col;
        let two = if i + 1 < n {
            Some((bytes[i], bytes[i + 1]))
        } else {
            None
        };
        if let Some(pair) = two {
            let kind2 = match pair {
                (b'=', b'=') => Some(CTokKind::EqEq),
                (b'!', b'=') => Some(CTokKind::BangEq),
                (b'<', b'=') => Some(CTokKind::Le),
                (b'>', b'=') => Some(CTokKind::Ge),
                (b'&', b'&') => Some(CTokKind::AmpAmp),
                (b'|', b'|') => Some(CTokKind::PipePipe),
                (b'+', b'=') => Some(CTokKind::PlusEq),
                (b'-', b'=') => Some(CTokKind::MinusEq),
                (b'+', b'+') => Some(CTokKind::PlusPlus),
                (b':', b':') => Some(CTokKind::ColonColon),
                _ => None,
            };
            if let Some(k) = kind2 {
                tokens.push(CTok {
                    kind: k,
                    line,
                    col: start_col,
                });
                i += 2;
                col += 2;
                continue;
            }
        }

        let kind1 = match b {
            b'(' => CTokKind::LParen,
            b')' => CTokKind::RParen,
            b'{' => CTokKind::LBrace,
            b'}' => CTokKind::RBrace,
            b'[' => CTokKind::LBracket,
            b']' => CTokKind::RBracket,
            b',' => CTokKind::Comma,
            b';' => CTokKind::Semi,
            b':' => CTokKind::Colon,
            b'?' => CTokKind::Question,
            b'.' => CTokKind::Dot,
            b'&' => CTokKind::Amp,
            b'*' => CTokKind::Star,
            b'+' => CTokKind::Plus,
            b'-' => CTokKind::Minus,
            b'/' => CTokKind::Slash,
            b'%' => CTokKind::Percent,
            b'!' => CTokKind::Bang,
            b'=' => CTokKind::Eq,
            b'<' => CTokKind::Lt,
            b'>' => CTokKind::Gt,
            other => {
                return Err(Diagnostic::new(
                    "c",
                    format!("unexpected character '{}'", other as char),
                    line,
                    start_col,
                ))
            }
        };
        tokens.push(CTok {
            kind: kind1,
            line,
            col: start_col,
        });
        i += 1;
        col += 1;
    }

    Ok(tokens)
}

fn parse_starlist_ident(ident: &str) -> Option<Type> {
    let rest = ident.strip_prefix("StarList_")?;
    let elem = match rest {
        "int64_t" => Type::Int,
        "double" => Type::Float,
        "bool" => Type::Bool,
        "str" => Type::Str,
        other if other.starts_with("StarList_") => parse_starlist_ident(other)?,
        other => Type::Named(other.to_string()),
    };
    Some(Type::list(elem))
}

fn prescan_c_types(
    tokens: &[CTok],
    known_enums: &mut HashSet<String>,
    struct_fields: &mut HashMap<String, Vec<(String, Type)>>,
) {
    let mut i = 0;
    while i + 2 < tokens.len() {
        if matches!(&tokens[i].kind, CTokKind::Ident(s) if s == "typedef") {
            if matches!(&tokens[i + 1].kind, CTokKind::Ident(s) if s == "enum") {
                if let CTokKind::Ident(ename) = &tokens[i + 2].kind {
                    known_enums.insert(ename.clone());
                }
            } else if matches!(&tokens[i + 1].kind, CTokKind::Ident(s) if s == "struct") {
                if let CTokKind::Ident(sname) = &tokens[i + 2].kind {
                    if !sname.starts_with("StarList_") {
                        struct_fields.entry(sname.clone()).or_default();
                    }
                }
            }
        }
        i += 1;
    }
}

struct CParser {
    tokens: Vec<CTok>,
    pos: usize,
    known_enums: HashSet<String>,
    struct_fields: HashMap<String, Vec<(String, Type)>>,
    local_types: HashMap<String, Type>,
    param_types: HashMap<String, Type>,
}

impl CParser {
    fn peek(&self) -> Option<&CTok> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&CTokKind> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn cur_loc(&self) -> (usize, usize) {
        self.peek()
            .or_else(|| self.tokens.last())
            .map(|t| (t.line, t.col))
            .unwrap_or((1, 1))
    }

    fn err<T>(&self, msg: impl Into<String>) -> Result<T, Diagnostic> {
        let (l, c) = self.cur_loc();
        Err(Diagnostic::new("c", msg, l, c))
    }

    fn next(&mut self) -> Option<CTok> {
        let t = self.tokens.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
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

    fn expect(&mut self, kind: &CTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(kind) {
            Ok(())
        } else {
            self.err(format!("expected {}", label))
        }
    }

    fn expect_ident(&mut self, ctx: &str) -> Result<String, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(CTokKind::Ident(s)) => {
                self.pos += 1;
                Ok(s)
            }
            _ => self.err(format!("expected identifier ({})", ctx)),
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
                None => return self.err("unclosed '{'"),
            }
        }
        Ok(())
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut items = Vec::new();
        let mut pending_comments: Vec<String> = Vec::new();

        while self.pos < self.tokens.len() {
            if let Some(CTokKind::Comment(c)) = self.peek_kind().cloned() {
                self.pos += 1;
                pending_comments.push(c);
                continue;
            }

            // Skip generated `static inline ... { ... }` helpers
            if self.eat_kw("static") {
                let _ = self.eat_kw("inline");
                while self.pos < self.tokens.len()
                    && !matches!(self.peek_kind(), Some(CTokKind::LBrace | CTokKind::Semi))
                {
                    self.pos += 1;
                }
                if self.peek_kind() == Some(&CTokKind::LBrace) {
                    self.skip_balanced_braces()?;
                } else {
                    let _ = self.eat(&CTokKind::Semi);
                }
                pending_comments.clear();
                continue;
            }

            if self.eat_kw("typedef") {
                if self.eat_kw("enum") {
                    let comments = std::mem::take(&mut pending_comments);
                    items.push(Item::Enum(self.parse_typedef_enum(comments)?));
                    continue;
                }
                if self.eat_kw("struct") {
                    if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s.starts_with("StarList_"))
                    {
                        let _ = self.next();
                        self.skip_balanced_braces()?;
                        let _ = self.expect_ident("StarList typedef alias")?;
                        self.expect(&CTokKind::Semi, "';'")?;
                        pending_comments.clear();
                        continue;
                    }
                    let comments = std::mem::take(&mut pending_comments);
                    items.push(Item::Struct(self.parse_typedef_struct(comments)?));
                    continue;
                }
                return self.err("expected 'enum' or 'struct' after 'typedef'");
            }

            // Function, test, or forward prototype
            let comments = std::mem::take(&mut pending_comments);
            let ret_ty = self.parse_type()?;
            let fn_name = self.expect_ident("function name")?;
            let params = self.parse_param_list()?;

            // Forward prototype ending in `;` -> skip!
            if self.eat(&CTokKind::Semi) {
                continue;
            }

            self.local_types.clear();
            self.param_types.clear();
            for p in &params {
                self.param_types.insert(p.name.clone(), p.ty.clone());
            }

            let mut body = self.parse_block()?;

            if fn_name.starts_with("test_") && params.is_empty() && ret_ty == Type::Void {
                let tname = fn_name
                    .strip_prefix("test_")
                    .unwrap_or(&fn_name)
                    .to_string();
                items.push(Item::Test(TestDecl {
                    id: 0,
                    name: tname,
                    body,
                    comments,
                    meta: Metadata::new(),
                }));
            } else {
                let actual_ret = if fn_name == "main" && params.is_empty() {
                    if matches!(body.last(), Some(Stmt::Return { value: Some(Expr::Int(0)), .. })) {
                        body.pop();
                    }
                    Type::Void
                } else {
                    ret_ty
                };
                items.push(Item::Function(FnDecl {
                    id: 0,
                    name: fn_name,
                    params,
                    ret_ty: actual_ret,
                    body,
                    comments,
                    meta: Metadata::new(),
                }));
            }
        }

        Ok(HubModule { items, next_id: 1 })
    }

    fn parse_typedef_enum(&mut self, comments: Vec<String>) -> Result<EnumDecl, Diagnostic> {
        let opt_tag = if let Some(CTokKind::Ident(_)) = self.peek_kind() {
            Some(self.expect_ident("enum tag")?)
        } else {
            None
        };
        self.expect(&CTokKind::LBrace, "'{' in enum")?;
        let mut raw_variants = Vec::new();
        while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
            if let Some(CTokKind::Comment(_)) = self.peek_kind() {
                self.pos += 1;
                continue;
            }
            let v = self.expect_ident("enum variant")?;
            if self.eat(&CTokKind::Eq) {
                let _ = self.eat(&CTokKind::Minus);
                let _ = self.next();
            }
            let _ = self.eat(&CTokKind::Comma);
            raw_variants.push(v);
        }
        self.expect(&CTokKind::RBrace, "'}' after enum")?;
        let alias = self.expect_ident("enum typedef name")?;
        self.expect(&CTokKind::Semi, "';' after typedef enum")?;
        let name = opt_tag.unwrap_or(alias);
        let prefix = format!("{}_", name);
        let variants: Vec<String> = raw_variants
            .into_iter()
            .map(|v| {
                v.strip_prefix(&prefix)
                    .map(|s| s.to_string())
                    .unwrap_or(v)
            })
            .collect();
        self.known_enums.insert(name.clone());
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_typedef_struct(&mut self, comments: Vec<String>) -> Result<StructDecl, Diagnostic> {
        let opt_tag = if let Some(CTokKind::Ident(_)) = self.peek_kind() {
            Some(self.expect_ident("struct tag")?)
        } else {
            None
        };
        self.expect(&CTokKind::LBrace, "'{' in struct")?;
        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
            if let Some(CTokKind::Comment(_)) = self.peek_kind() {
                self.pos += 1;
                continue;
            }
            if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "uint8_t")
                && matches!(self.tokens.get(self.pos + 1).map(|t| &t.kind), Some(CTokKind::Ident(f)) if f == "_empty")
            {
                self.pos += 2;
                self.expect(&CTokKind::Semi, "';'")?;
                continue;
            }
            let fty = self.parse_type()?;
            let fname = self.expect_ident("struct field name")?;
            self.expect(&CTokKind::Semi, "';' after struct field")?;
            fields.push(Field {
                id: 0,
                name: fname,
                ty: fty,
                meta: Metadata::new(),
            });
        }
        self.expect(&CTokKind::RBrace, "'}' after struct")?;
        let alias = self.expect_ident("struct typedef name")?;
        self.expect(&CTokKind::Semi, "';' after typedef struct")?;
        let name = opt_tag.unwrap_or(alias);
        self.struct_fields.insert(
            name.clone(),
            fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect(),
        );
        Ok(StructDecl {
            id: 0,
            name,
            fields,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_type(&mut self) -> Result<Type, Diagnostic> {
        let (ty, _) = self.parse_var_decl_type()?;
        Ok(ty)
    }

    fn parse_var_decl_type(&mut self) -> Result<(Type, bool), Diagnostic> {
        let mut leading_const = false;
        while self.eat_kw("const") {
            leading_const = true;
        }
        let _ = self.eat_kw("struct");
        let _ = self.eat_kw("enum");
        let base = self.expect_ident("type name")?;
        if base == "char" && self.eat(&CTokKind::Star) {
            let ptr_const = self.eat_kw("const");
            return Ok((Type::Str, ptr_const));
        }
        if let Some(lt) = parse_starlist_ident(&base) {
            return Ok((lt, leading_const));
        }
        let ty = match base.as_str() {
            "int64_t" | "int32_t" | "int" | "long" => {
                if base == "long" {
                    let _ = self.eat_kw("long");
                }
                Type::Int
            }
            "double" | "float" => Type::Float,
            "bool" | "_Bool" => Type::Bool,
            "void" => Type::Void,
            other => Type::Named(other.to_string()),
        };
        Ok((ty, leading_const))
    }

    fn parse_param_list(&mut self) -> Result<Vec<Param>, Diagnostic> {
        self.expect(&CTokKind::LParen, "'('")?;
        if self.eat(&CTokKind::RParen) {
            return Ok(Vec::new());
        }
        if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "void")
            && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&CTokKind::RParen)
        {
            self.pos += 2;
            return Ok(Vec::new());
        }
        let mut params = Vec::new();
        loop {
            let ty = self.parse_type()?;
            let name = self.expect_ident("parameter name")?;
            params.push(Param {
                id: 0,
                name,
                ty,
                meta: Metadata::new(),
            });
            if !self.eat(&CTokKind::Comma) {
                break;
            }
        }
        self.expect(&CTokKind::RParen, "')'")?;
        Ok(params)
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        self.expect(&CTokKind::LBrace, "'{'")?;
        let mut stmts = Vec::new();
        while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
            if let Some(s) = self.parse_stmt_opt()? {
                stmts.push(s);
            }
        }
        self.expect(&CTokKind::RBrace, "'}'")?;
        Ok(stmts)
    }

    fn looks_like_var_decl(&self) -> bool {
        let mut p = self.pos;
        let mut had_const = false;
        if matches!(self.tokens.get(p).map(|t| &t.kind), Some(CTokKind::Ident(s)) if s == "const") {
            had_const = true;
            p += 1;
        }
        if had_const {
            return true;
        }
        if matches!(
            self.tokens.get(p).map(|t| &t.kind),
            Some(CTokKind::Ident(s)) if s == "struct" || s == "enum"
        ) {
            return true;
        }
        let Some(CTokKind::Ident(ty_ident)) = self.tokens.get(p).map(|t| &t.kind) else {
            return false;
        };
        if ty_ident == "char"
            && self.tokens.get(p + 1).map(|t| &t.kind) == Some(&CTokKind::Star)
            && matches!(
                self.tokens.get(p + 2).map(|t| &t.kind),
                Some(CTokKind::Ident(_))
            )
        {
            return true;
        }
        let is_known_ty = matches!(
            ty_ident.as_str(),
            "int64_t" | "int32_t" | "int" | "long" | "double" | "float" | "bool" | "_Bool"
        ) || ty_ident.starts_with("StarList_")
            || self.struct_fields.contains_key(ty_ident)
            || self.known_enums.contains(ty_ident);
        is_known_ty
            && matches!(
                self.tokens.get(p + 1).map(|t| &t.kind),
                Some(CTokKind::Ident(_))
            )
    }

    fn parse_stmt_opt(&mut self) -> Result<Option<Stmt>, Diagnostic> {
        if let Some(CTokKind::Comment(c)) = self.peek_kind().cloned() {
            self.pos += 1;
            if c.trim() == "@star-match" && self.eat_kw("if") {
                return Ok(Some(self.parse_star_string_match()?));
            }
            return Ok(Some(Stmt::Comment { id: 0, text: c }));
        }

        // Skip `__builtin_unreachable();`
        if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "__builtin_unreachable") {
            self.pos += 1;
            self.expect(&CTokKind::LParen, "'('")?;
            self.expect(&CTokKind::RParen, "')'")?;
            self.expect(&CTokKind::Semi, "';'")?;
            return Ok(None);
        }

        // Braced `{ const StarList_... _iter_N = <iter>; for (...) { ... } }` lowered ForEach!
        if self.peek_kind() == Some(&CTokKind::LBrace) {
            return Ok(Some(self.parse_braced_foreach()?));
        }

        if self.eat_kw("if") {
            return Ok(Some(self.parse_if()?));
        }
        if self.eat_kw("switch") {
            return Ok(Some(self.parse_switch()?));
        }
        if self.eat_kw("while") {
            self.expect(&CTokKind::LParen, "'(' after while")?;
            let cond = self.parse_expr()?;
            self.expect(&CTokKind::RParen, "')'")?;
            let body = self.parse_block()?;
            return Ok(Some(Stmt::While {
                id: 0,
                cond,
                body,
                meta: Metadata::new(),
            }));
        }
        if self.eat_kw("for") {
            return Ok(Some(self.parse_for()?));
        }
        if self.eat_kw("break") {
            self.expect(&CTokKind::Semi, "';'")?;
            return Ok(Some(Stmt::Break { id: 0 }));
        }
        if self.eat_kw("continue") {
            self.expect(&CTokKind::Semi, "';'")?;
            return Ok(Some(Stmt::Continue { id: 0 }));
        }
        if self.eat_kw("return") {
            if self.eat(&CTokKind::Semi) {
                return Ok(Some(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                }));
            }
            let val = self.parse_expr()?;
            self.expect(&CTokKind::Semi, "';'")?;
            return Ok(Some(Stmt::Return {
                id: 0,
                value: Some(val),
                meta: Metadata::new(),
            }));
        }

        // `assert(...);`
        if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "assert")
            && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&CTokKind::LParen)
        {
            self.pos += 2;
            let cond = self.parse_expr()?;
            self.expect(&CTokKind::RParen, "')' after assert")?;
            self.expect(&CTokKind::Semi, "';' after assert")?;
            return Ok(Some(Stmt::Assert {
                id: 0,
                cond,
                meta: Metadata::new(),
            }));
        }

        // Local declaration `[const] <Type> [const] <name> = <val>;`
        if self.looks_like_var_decl() {
            let (ty, is_const) = self.parse_var_decl_type()?;
            let name = self.expect_ident("variable name")?;
            self.expect(&CTokKind::Eq, "'=' in variable declaration")?;
            let val = if self.peek_kind() == Some(&CTokKind::LBrace) {
                // `{0}` or `{}` empty list initializer
                self.pos += 1;
                let _ = self.eat(&CTokKind::Int(0));
                self.expect(&CTokKind::RBrace, "'}'")?;
                Expr::List(Vec::new())
            } else {
                self.parse_expr()?
            };
            self.expect(&CTokKind::Semi, "';' after declaration")?;
            let mut meta = Metadata::new();
            if !is_const {
                meta.insert("explicit_mut".to_string(), "true".to_string());
            }
            self.local_types.insert(name.clone(), ty.clone());
            return Ok(Some(Stmt::Let {
                id: 0,
                name,
                mutable: !is_const,
                ty: Some(ty),
                value: val,
                meta,
            }));
        }

        // Expression or assignment statement
        let lhs = self.parse_expr()?;
        let assign_op = if self.eat(&CTokKind::Eq) {
            Some(AssignOp::Set)
        } else if self.eat(&CTokKind::PlusEq) {
            Some(AssignOp::AddAssign)
        } else if self.eat(&CTokKind::MinusEq) {
            Some(AssignOp::SubAssign)
        } else {
            None
        };

        if let Some(op) = assign_op {
            let rhs = self.parse_expr()?;
            self.expect(&CTokKind::Semi, "';' after assignment")?;
            let target = match lhs {
                Expr::Var(v) => AssignTarget::Var(v),
                Expr::FieldAccess { base, field } => match *base {
                    Expr::Var(b) => AssignTarget::Field { base: b, field },
                    _ => return self.err("field assignment base must be a variable"),
                },
                Expr::Index { base, index } => match *base {
                    Expr::Var(b) => AssignTarget::Index {
                        base: b,
                        index: *index,
                    },
                    _ => return self.err("index assignment base must be a variable"),
                },
                _ => return self.err("invalid assignment target"),
            };
            return Ok(Some(Stmt::Assign {
                id: 0,
                target,
                op,
                value: rhs,
                meta: Metadata::new(),
            }));
        }

        self.expect(&CTokKind::Semi, "';' after expression")?;
        Ok(Some(Stmt::Expr {
            id: 0,
            expr: lhs,
            meta: Metadata::new(),
        }))
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
        let mut scrutinee: Option<Expr> = None;
        let mut arms = Vec::new();
        loop {
            self.expect(&CTokKind::LParen, "'(' in @star-match")?;
            let cond = self.parse_expr()?;
            self.expect(&CTokKind::RParen, "')' in @star-match")?;
            let body = self.parse_block()?;
            match cond {
                Expr::Bool(true) => {
                    arms.push(MatchArm {
                        pat: MatchPat::Wildcard,
                        body,
                    });
                }
                Expr::Binary {
                    op: BinOp::Eq,
                    left,
                    right,
                } => {
                    if scrutinee.is_none() {
                        scrutinee = Some(*left);
                    }
                    let pat = match *right {
                        Expr::Str(s) => MatchPat::Str(s),
                        Expr::Int(v) => MatchPat::Int(v),
                        _ => return self.err("expected literal pattern in @star-match"),
                    };
                    arms.push(MatchArm { pat, body });
                }
                _ => return self.err("malformed @star-match condition"),
            }
            if self.eat_kw("else") {
                if self.eat_kw("if") {
                    continue;
                }
                let wild_body = self.parse_block()?;
                arms.push(MatchArm {
                    pat: MatchPat::Wildcard,
                    body: wild_body,
                });
                break;
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
        let scrut = self.parse_expr()?;
        self.expect(&CTokKind::RParen, "')'")?;
        self.expect(&CTokKind::LBrace, "'{' after switch")?;
        let mut arms = Vec::new();
        while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
            let pat = if self.eat_kw("default") {
                self.expect(&CTokKind::Colon, "':' after default")?;
                MatchPat::Wildcard
            } else if self.eat_kw("case") {
                let p = if self.eat(&CTokKind::Minus) {
                    match self.next().map(|t| t.kind) {
                        Some(CTokKind::Int(v)) => MatchPat::Int(-v),
                        _ => return self.err("expected integer after '-' in case"),
                    }
                } else {
                    match self.next().map(|t| t.kind) {
                        Some(CTokKind::Int(v)) => MatchPat::Int(v),
                        Some(CTokKind::Ident(id)) => {
                            if self.eat(&CTokKind::ColonColon) {
                                let v = self.expect_ident("enum variant")?;
                                MatchPat::EnumVariant {
                                    enum_name: id,
                                    variant: v,
                                }
                            } else if let Some((en, vr)) = self.split_enum_ident(&id) {
                                MatchPat::EnumVariant {
                                    enum_name: en,
                                    variant: vr,
                                }
                            } else {
                                return self.err(format!("unknown enum case '{}'", id));
                            }
                        }
                        _ => return self.err("expected case pattern"),
                    }
                };
                self.expect(&CTokKind::Colon, "':' after case")?;
                p
            } else {
                return self.err("expected 'case' or 'default' in switch");
            };

            let mut body = if self.peek_kind() == Some(&CTokKind::LBrace) {
                self.parse_block()?
            } else {
                let mut b = Vec::new();
                while !matches!(
                    self.peek_kind(),
                    Some(CTokKind::RBrace) | None
                ) && !matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "case" || s == "default")
                {
                    if let Some(s) = self.parse_stmt_opt()? {
                        b.push(s);
                    }
                }
                b
            };
            if matches!(body.last(), Some(Stmt::Break { .. })) {
                body.pop();
            }
            arms.push(MatchArm { pat, body });
        }
        self.expect(&CTokKind::RBrace, "'}' after switch")?;
        Ok(Stmt::Match {
            id: 0,
            expr: scrut,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_for(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&CTokKind::LParen, "'(' after for")?;
        let _ = self.parse_type()?;
        let idx_var = self.expect_ident("for loop variable")?;
        self.expect(&CTokKind::Eq, "'=' in for")?;
        let start = self.parse_expr()?;
        self.expect(&CTokKind::Semi, "';' in for")?;

        let cmp_lhs = self.expect_ident("for condition variable")?;
        if cmp_lhs != idx_var {
            return self.err("for condition variable must match loop variable");
        }
        self.expect(&CTokKind::Lt, "'<' in for condition")?;
        let end = self.parse_expr()?;
        self.expect(&CTokKind::Semi, "';' after for condition")?;

        let inc_var = self.expect_ident("for increment variable")?;
        if inc_var != idx_var {
            return self.err("for increment variable must match loop variable");
        }
        if self.eat(&CTokKind::PlusPlus) {
            // `i++`
        } else if self.eat(&CTokKind::PlusEq) {
            let _ = self.parse_expr()?;
        } else {
            return self.err("expected '++' or '+=' in for header");
        }
        self.expect(&CTokKind::RParen, "')' after for")?;

        self.local_types.insert(idx_var.clone(), Type::Int);
        let mut body = self.parse_block()?;

        // Recognize `ForEach` pattern:
        // `for (int64_t _idx_N = 0; _idx_N < <iter>.len; _idx_N++) { const T <var> = <iter>.data[_idx_N]; ... }`
        if idx_var.starts_with("_idx_") && start == Expr::Int(0) {
            if let Expr::Intrinsic(intr) = &end {
                if let Intrinsic::Len(iter_expr) = intr.as_ref() {
                    if let Some(Stmt::Let {
                        name: elem_var,
                        value:
                            Expr::Index {
                                base: idx_base,
                                index: idx_expr,
                            },
                        ..
                    }) = body.first()
                    {
                        if idx_base.as_ref() == iter_expr && **idx_expr == Expr::Var(idx_var.clone())
                        {
                            let var = elem_var.clone();
                            let iter = iter_expr.clone();
                            body.remove(0);
                            return Ok(Stmt::ForEach {
                                id: 0,
                                var,
                                iter,
                                body,
                                meta: Metadata::new(),
                            });
                        }
                    }
                }
            }
        }

        self.local_types.insert(idx_var.clone(), Type::Int);
        Ok(Stmt::ForRange {
            id: 0,
            var: idx_var,
            start,
            end,
            body,
            meta: Metadata::new(),
        })
    }

    fn parse_braced_foreach(&mut self) -> Result<Stmt, Diagnostic> {
        let mut block = self.parse_block()?;
        if block.len() == 2 {
            if let Stmt::Let {
                name: iter_tmp,
                value: iter_val,
                ..
            } = &block[0]
            {
                if iter_tmp.starts_with("_iter_") {
                    if let Stmt::ForEach {
                        var,
                        iter: Expr::Var(v),
                        body,
                        meta,
                        ..
                    } = &block[1]
                    {
                        if v == iter_tmp {
                            return Ok(Stmt::ForEach {
                                id: 0,
                                var: var.clone(),
                                iter: iter_val.clone(),
                                body: body.clone(),
                                meta: meta.clone(),
                            });
                        }
                    }
                }
            }
        }
        if block.len() == 1 {
            return Ok(block.remove(0));
        }
        self.err("unexpected standalone braced block")
    }

    fn split_enum_ident(&self, ident: &str) -> Option<(String, String)> {
        // Match longest known enum prefix `<EnumName>_<Variant>`
        let mut best: Option<(String, String)> = None;
        for en in &self.known_enums {
            let pref = format!("{}_", en);
            if let Some(rest) = ident.strip_prefix(&pref) {
                if !rest.is_empty()
                    && best.as_ref().map(|(b, _)| en.len() > b.len()).unwrap_or(true) {
                        best = Some((en.clone(), rest.to_string()));
                    }
            }
        }
        best
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
            let op = if self.eat(&CTokKind::EqEq) {
                Some(BinOp::Eq)
            } else if self.eat(&CTokKind::BangEq) {
                Some(BinOp::Ne)
            } else if self.eat(&CTokKind::Lt) {
                Some(BinOp::Lt)
            } else if self.eat(&CTokKind::Le) {
                Some(BinOp::Le)
            } else if self.eat(&CTokKind::Gt) {
                Some(BinOp::Gt)
            } else if self.eat(&CTokKind::Ge) {
                Some(BinOp::Ge)
            } else {
                None
            };
            if let Some(bop) = op {
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
            let op = if self.eat(&CTokKind::Plus) {
                Some(BinOp::Add)
            } else if self.eat(&CTokKind::Minus) {
                Some(BinOp::Sub)
            } else {
                None
            };
            if let Some(bop) = op {
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
            let op = if self.eat(&CTokKind::Star) {
                Some(BinOp::Mul)
            } else if self.eat(&CTokKind::Slash) {
                Some(BinOp::Div)
            } else if self.eat(&CTokKind::Percent) {
                Some(BinOp::Mod)
            } else {
                None
            };
            if let Some(bop) = op {
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

        // C casts & compound literals: `(<Type>)...`
        if self.peek_kind() == Some(&CTokKind::LParen) {
            if let Some(res) = self.try_parse_cast_or_compound_literal()? {
                return self.parse_postfix_tail(res);
            }
        }

        self.parse_postfix()
    }

    fn try_parse_cast_or_compound_literal(&mut self) -> Result<Option<Expr>, Diagnostic> {
        let saved_pos = self.pos;
        self.pos += 1; // skip `(`

        // Check if `(long long)` or `(int64_t)` or `(<StructName>){ ... }` or `(StarList_...){0}`
        if matches!(self.peek_kind(), Some(CTokKind::Ident(s)) if s == "long") {
            self.pos += 1;
            let _ = self.eat_kw("long");
            if self.eat(&CTokKind::RParen) {
                let inner = self.parse_unary()?;
                return Ok(Some(inner));
            }
            self.pos = saved_pos;
            return Ok(None);
        }

        if let Some(CTokKind::Ident(ident)) = self.peek_kind().cloned() {
            if matches!(ident.as_str(), "int64_t" | "int32_t" | "int" | "double") {
                self.pos += 1;
                if self.eat(&CTokKind::RParen) {
                    let inner = self.parse_unary()?;
                    return Ok(Some(inner));
                }
                self.pos = saved_pos;
                return Ok(None);
            }

            if ident.starts_with("StarList_") {
                self.pos += 1;
                if self.eat(&CTokKind::RParen) && self.eat(&CTokKind::LBrace) {
                    let _ = self.eat(&CTokKind::Int(0));
                    self.expect(&CTokKind::RBrace, "'}'")?;
                    return Ok(Some(Expr::List(Vec::new())));
                }
                self.pos = saved_pos;
                return Ok(None);
            }

            if self.struct_fields.contains_key(&ident) {
                self.pos += 1;
                if self.eat(&CTokKind::RParen) && self.eat(&CTokKind::LBrace) {
                    let mut fields = Vec::new();
                    let mut idx = 0usize;
                    let decl_order = self
                        .struct_fields
                        .get(&ident)
                        .cloned()
                        .unwrap_or_default();
                    while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
                        if self.eat(&CTokKind::Dot) {
                            let fname = self.expect_ident("designated field name")?;
                            self.expect(&CTokKind::Eq, "'=' after designated field")?;
                            let fval = self.parse_expr()?;
                            if fname != "_empty" {
                                fields.push((fname, fval));
                            }
                        } else {
                            let fval = self.parse_expr()?;
                            let fname = decl_order
                                .get(idx)
                                .map(|(n, _)| n.clone())
                                .unwrap_or_else(|| format!("f{}", idx));
                            fields.push((fname, fval));
                            idx += 1;
                        }
                        if !self.eat(&CTokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&CTokKind::RBrace, "'}' after compound literal")?;
                    return Ok(Some(Expr::StructInit {
                        name: ident,
                        fields,
                    }));
                }
                self.pos = saved_pos;
                return Ok(None);
            }
        }

        self.pos = saved_pos;
        Ok(None)
    }

    fn parse_postfix(&mut self) -> Result<Expr, Diagnostic> {
        let base = self.parse_primary()?;
        self.parse_postfix_tail(base)
    }

    fn parse_postfix_tail(&mut self, mut expr: Expr) -> Result<Expr, Diagnostic> {
        loop {
            if self.eat(&CTokKind::Dot) {
                let field = self.expect_ident("field name")?;
                if field == "data" && self.eat(&CTokKind::LBracket) {
                    let idx = self.parse_expr()?;
                    self.expect(&CTokKind::RBracket, "']'")?;
                    expr = Expr::Index {
                        base: Box::new(expr),
                        index: Box::new(idx),
                    };
                } else if field == "len" {
                    let is_user_struct_len = match &expr {
                        Expr::Var(v) => self
                            .local_types
                            .get(v)
                            .or_else(|| self.param_types.get(v))
                            .and_then(|t| match t {
                                Type::Named(sn) => self.struct_fields.get(sn),
                                _ => None,
                            })
                            .map(|fs| fs.iter().any(|(fnm, _)| fnm == "len"))
                            .unwrap_or(false),
                        _ => false,
                    };
                    if is_user_struct_len {
                        expr = Expr::FieldAccess {
                            base: Box::new(expr),
                            field,
                        };
                    } else {
                        expr = Expr::intrinsic(Intrinsic::Len(expr));
                    }
                } else {
                    expr = Expr::FieldAccess {
                        base: Box::new(expr),
                        field,
                    };
                }
            } else if self.eat(&CTokKind::LBracket) {
                let idx = self.parse_expr()?;
                self.expect(&CTokKind::RBracket, "']'")?;
                expr = Expr::Index {
                    base: Box::new(expr),
                    index: Box::new(idx),
                };
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Expr, Diagnostic> {
        match self.peek_kind().cloned() {
            Some(CTokKind::Int(v)) => {
                self.pos += 1;
                Ok(Expr::Int(v))
            }
            Some(CTokKind::Float(v)) => {
                self.pos += 1;
                Ok(Expr::Float(v))
            }
            Some(CTokKind::Str(s)) => {
                self.pos += 1;
                Ok(Expr::Str(s))
            }
            Some(CTokKind::LParen) => {
                self.pos += 1;
                let inner = self.parse_expr()?;
                // Handle boolean print ternary `((cond) ? "true" : "false")`
                if self.eat(&CTokKind::Question) {
                    let t_val = self.parse_expr()?;
                    self.expect(&CTokKind::Colon, "':' in ternary")?;
                    let f_val = self.parse_expr()?;
                    self.expect(&CTokKind::RParen, "')' after ternary")?;
                    if t_val == Expr::Str("true".to_string())
                        && f_val == Expr::Str("false".to_string())
                    {
                        return Ok(inner);
                    }
                    return self.err("unsupported ternary expression");
                }
                self.expect(&CTokKind::RParen, "')'")?;
                Ok(inner)
            }
            Some(CTokKind::Ident(id)) => {
                self.pos += 1;
                if id == "true" {
                    return Ok(Expr::Bool(true));
                }
                if id == "false" {
                    return Ok(Expr::Bool(false));
                }
                if self.eat(&CTokKind::ColonColon) {
                    let v = self.expect_ident("enum variant")?;
                    return Ok(Expr::EnumVariant {
                        enum_name: id,
                        variant: v,
                    });
                }

                // Function or runtime helper call
                if self.peek_kind() == Some(&CTokKind::LParen) {
                    return self.parse_call_or_intrinsic(id);
                }

                if !self.local_types.contains_key(&id) && !self.param_types.contains_key(&id) {
                    if let Some((en, vr)) = self.split_enum_ident(&id) {
                        return Ok(Expr::EnumVariant {
                            enum_name: en,
                            variant: vr,
                        });
                    }
                }
                Ok(Expr::Var(id))
            }
            _ => self.err("expected expression"),
        }
    }

    fn parse_call_or_intrinsic(&mut self, name: String) -> Result<Expr, Diagnostic> {
        // `StarList_<slug>_of((const <ElemC>[]){ e1, e2, ... }, N)`
        if name.starts_with("StarList_") && name.ends_with("_of") {
            self.expect(&CTokKind::LParen, "'('")?;
            self.expect(&CTokKind::LParen, "'(' before compound array")?;
            let _ = self.parse_type()?;
            self.expect(&CTokKind::LBracket, "'['")?;
            self.expect(&CTokKind::RBracket, "']'")?;
            self.expect(&CTokKind::RParen, "')'")?;
            self.expect(&CTokKind::LBrace, "'{'")?;
            let mut items = Vec::new();
            while !matches!(self.peek_kind(), Some(CTokKind::RBrace) | None) {
                items.push(self.parse_expr()?);
                if !self.eat(&CTokKind::Comma) {
                    break;
                }
            }
            self.expect(&CTokKind::RBrace, "'}'")?;
            self.expect(&CTokKind::Comma, "',' before list length")?;
            let _ = self.parse_expr()?;
            self.expect(&CTokKind::RParen, "')'")?;
            return Ok(Expr::List(items));
        }

        // `StarList_<slug>_push(&list, val)`
        if name.starts_with("StarList_") && name.ends_with("_push") {
            self.expect(&CTokKind::LParen, "'('")?;
            let _ = self.eat(&CTokKind::Amp);
            let list = self.parse_expr()?;
            self.expect(&CTokKind::Comma, "','")?;
            let value = self.parse_expr()?;
            self.expect(&CTokKind::RParen, "')'")?;
            return Ok(Expr::intrinsic(Intrinsic::Push { list, value }));
        }

        let args = self.parse_call_args()?;

        match name.as_str() {
            "printf" => {
                if args.is_empty() {
                    return Ok(Expr::intrinsic(Intrinsic::Print(Vec::new())));
                }
                if args.len() == 1 && args[0] == Expr::Str("\n".to_string()) {
                    return Ok(Expr::intrinsic(Intrinsic::Print(Vec::new())));
                }
                // `args[0]` is format string `"%s %lld\n"`, `args[1..]` are printed expressions
                Ok(Expr::intrinsic(Intrinsic::Print(args[1..].to_vec())))
            }
            "puts" if args.len() == 1 => {
                Ok(Expr::intrinsic(Intrinsic::Print(vec![args[0].clone()])))
            }
            "strlen" if args.len() == 1 => Ok(Expr::intrinsic(Intrinsic::Len(args[0].clone()))),
            "star_min_i64" | "fmin" if args.len() == 2 => Ok(Expr::intrinsic(Intrinsic::Min(
                args[0].clone(),
                args[1].clone(),
            ))),
            "star_max_i64" | "fmax" if args.len() == 2 => Ok(Expr::intrinsic(Intrinsic::Max(
                args[0].clone(),
                args[1].clone(),
            ))),
            "star_abs_i64" | "fabs" | "llabs" | "abs" if args.len() == 1 => {
                Ok(Expr::intrinsic(Intrinsic::Abs(args[0].clone())))
            }
            "star_str_concat" if args.len() == 2 => Ok(Expr::Binary {
                op: BinOp::Add,
                left: Box::new(args[0].clone()),
                right: Box::new(args[1].clone()),
            }),
            "star_str_eq" if args.len() == 2 => Ok(Expr::Binary {
                op: BinOp::Eq,
                left: Box::new(args[0].clone()),
                right: Box::new(args[1].clone()),
            }),
            "star_str_ne" if args.len() == 2 => Ok(Expr::Binary {
                op: BinOp::Ne,
                left: Box::new(args[0].clone()),
                right: Box::new(args[1].clone()),
            }),
            "star_str_contains" if args.len() == 2 => Ok(Expr::intrinsic(Intrinsic::Contains {
                haystack: args[0].clone(),
                needle: args[1].clone(),
            })),
            "star_str_upper" if args.len() == 1 => {
                Ok(Expr::intrinsic(Intrinsic::Upper(args[0].clone())))
            }
            "star_str_lower" if args.len() == 1 => {
                Ok(Expr::intrinsic(Intrinsic::Lower(args[0].clone())))
            }
            "star_int_to_str" | "star_float_to_str" | "star_bool_to_str" | "star_str_id"
                if args.len() == 1 =>
            {
                Ok(Expr::intrinsic(Intrinsic::ToStr(args[0].clone())))
            }
            "star_fmt_f64" if args.len() == 1 => Ok(args[0].clone()),
            other => {
                if other.starts_with("StarList_") && other.ends_with("_contains") && args.len() == 2
                {
                    return Ok(Expr::intrinsic(Intrinsic::Contains {
                        haystack: args[0].clone(),
                        needle: args[1].clone(),
                    }));
                }
                if other.starts_with("StarList_") && other.ends_with("_eq") && args.len() == 2 {
                    return Ok(Expr::Binary {
                        op: BinOp::Eq,
                        left: Box::new(args[0].clone()),
                        right: Box::new(args[1].clone()),
                    });
                }
                if other.starts_with("StarList_") && other.ends_with("_ne") && args.len() == 2 {
                    return Ok(Expr::Binary {
                        op: BinOp::Ne,
                        left: Box::new(args[0].clone()),
                        right: Box::new(args[1].clone()),
                    });
                }
                if let Some(sname) = other.strip_suffix("_eq") {
                    if self.struct_fields.contains_key(sname) && args.len() == 2 {
                        return Ok(Expr::Binary {
                            op: BinOp::Eq,
                            left: Box::new(args[0].clone()),
                            right: Box::new(args[1].clone()),
                        });
                    }
                }
                if let Some(sname) = other.strip_suffix("_ne") {
                    if self.struct_fields.contains_key(sname) && args.len() == 2 {
                        return Ok(Expr::Binary {
                            op: BinOp::Ne,
                            left: Box::new(args[0].clone()),
                            right: Box::new(args[1].clone()),
                        });
                    }
                }
                Ok(Expr::Call { func: name, args })
            }
        }
    }

    fn parse_call_args(&mut self) -> Result<Vec<Expr>, Diagnostic> {
        self.expect(&CTokKind::LParen, "'('")?;
        if self.eat(&CTokKind::RParen) {
            return Ok(Vec::new());
        }
        let mut args = Vec::new();
        loop {
            args.push(self.parse_expr()?);
            if !self.eat(&CTokKind::Comma) {
                break;
            }
        }
        self.expect(&CTokKind::RParen, "')'")?;
        Ok(args)
    }
}

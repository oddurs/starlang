use std::collections::{HashMap, HashSet};

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl,
    HubModule, Intrinsic, Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl,
    Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct LuaLens;

const LUA_PREAMBLE: &str = r##"-- StarLang Lua / LuaJIT + LuaCATS Runtime Helpers
local function star_idiv(a, b)
    local q = a / b
    local r = q >= 0 and math.floor(q) or math.ceil(q)
    if r == 0 then return 0 end
    return r
end

local function star_irem(a, b)
    local r = a - star_idiv(a, b) * b
    if r == 0 then return 0 end
    return r
end

local function star_tostr(v)
    if v == 0 then return "0" end
    return tostring(v)
end

local function star_print(...)
    local n = select("#", ...)
    local parts = {}
    for i = 1, n do
        local v = select(i, ...)
        if v == 0 then v = 0 end
        parts[i] = tostring(v)
    end
    print(table.concat(parts, " "))
end

local function star_eql(a, b)
    if type(a) ~= type(b) then return false end
    if type(a) ~= "table" then return a == b end
    for k, v in pairs(a) do
        if not star_eql(v, b[k]) then return false end
    end
    for k, _ in pairs(b) do
        if a[k] == nil then return false end
    end
    return true
end

local function star_neql(a, b)
    return not star_eql(a, b)
end

local function star_assert_eq(a, b)
    if not star_eql(a, b) then
        error("assert_eq failed")
    end
end

local function star_contains(h, n)
    if type(h) == "string" then
        return string.find(h, n, 1, true) ~= nil
    end
    for i = 1, #h do
        if star_eql(h[i], n) then return true end
    end
    return false
end
-- @star-end-preamble
"##;

impl LanguageLens for LuaLens {
    fn id(&self) -> SpokeId {
        SpokeId::Lua
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut fmt = LuaFormatter::new(hub);
        fmt.format_module()
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_lua(source)?;
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
        prescan_lua_types(&tokens, &mut known_structs, &mut known_enums);

        let mut parser = LuaParser {
            tokens,
            pos: 0,
            known_structs,
            known_enums,
        };
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Lua))
    }
}

struct LuaFormatter<'a> {
    hub: &'a HubModule,
    struct_names: HashSet<String>,
    fn_ret_types: HashMap<String, Type>,
    struct_fields: HashMap<String, HashMap<String, Type>>,
    enum_names: HashSet<String>,
    env: HashMap<String, Type>,
    loop_depth: usize,
}

impl<'a> LuaFormatter<'a> {
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
            loop_depth: 0,
        }
    }

    fn format_module(&mut self) -> String {
        let mut out = String::from(LUA_PREAMBLE);
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
            out.push_str("\nmain()\n");
        }
        out
    }

    fn fmt_type(&self, ty: &Type) -> String {
        match ty {
            Type::Int => "integer".to_string(),
            Type::Float => "number".to_string(),
            Type::Bool => "boolean".to_string(),
            Type::Str => "string".to_string(),
            Type::Void => "nil".to_string(),
            Type::List(inner) => format!("{}[]", self.fmt_type(inner)),
            Type::Named(name) => name.clone(),
        }
    }

    fn fmt_enum(&self, e: &EnumDecl, out: &mut String) {
        for c in &e.comments {
            out.push_str(&format!("-- {}\n", c));
        }
        out.push_str(&format!("---@enum {}\n", e.name));
        out.push_str(&format!("local {} = {{\n", e.name));
        for (idx, v) in e.variants.iter().enumerate() {
            out.push_str(&format!("    {} = {},\n", v, idx));
        }
        out.push_str("}\n");
    }

    fn fmt_struct(&self, s: &StructDecl, out: &mut String) {
        for c in &s.comments {
            out.push_str(&format!("-- {}\n", c));
        }
        out.push_str(&format!("---@class {}\n", s.name));
        for f in &s.fields {
            out.push_str(&format!("---@field {} {}\n", f.name, self.fmt_type(&f.ty)));
        }
        out.push_str(&format!("local {} = {{}}\n", s.name));
        out.push_str(&format!("function {}.new(o) return o end\n", s.name));
    }

    fn fmt_fn(&mut self, f: &FnDecl, out: &mut String) {
        self.env.clear();
        self.loop_depth = 0;
        for c in &f.comments {
            out.push_str(&format!("-- {}\n", c));
        }
        for p in &f.params {
            self.env.insert(p.name.clone(), p.ty.clone());
            out.push_str(&format!("---@param {} {}\n", p.name, self.fmt_type(&p.ty)));
        }
        if f.ret_ty != Type::Void {
            out.push_str(&format!("---@return {}\n", self.fmt_type(&f.ret_ty)));
        }
        let param_names: Vec<&str> = f.params.iter().map(|p| p.name.as_str()).collect();
        out.push_str(&format!(
            "local function {}({})\n",
            f.name,
            param_names.join(", ")
        ));
        let mut list_hints = HashMap::new();
        self.collect_push_hints(&f.body, &mut list_hints);
        for stmt in &f.body {
            self.fmt_stmt(stmt, 1, &list_hints, out);
        }
        out.push_str("end\n");
    }

    fn fmt_test(&mut self, t: &TestDecl, out: &mut String) {
        self.env.clear();
        self.loop_depth = 0;
        for c in &t.comments {
            out.push_str(&format!("-- {}\n", c));
        }
        out.push_str(&format!("local function test_{}()\n", t.name));
        let mut list_hints = HashMap::new();
        self.collect_push_hints(&t.body, &mut list_hints);
        for stmt in &t.body {
            self.fmt_stmt(stmt, 1, &list_hints, out);
        }
        out.push_str("end\n");
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

    fn is_deep_eq_type(&self, ty: &Type) -> bool {
        match ty {
            Type::List(_) => true,
            Type::Named(n) => self.struct_names.contains(n),
            _ => false,
        }
    }

    fn target_type(&self, target: &AssignTarget) -> Option<Type> {
        match target {
            AssignTarget::Var(v) => self.env.get(v).cloned(),
            AssignTarget::Field { base, field } => {
                if let Some(Type::Named(sname)) = self.env.get(base) {
                    if let Some(s) = self.hub.find_struct(sname) {
                        return s.fields.iter().find(|f| &f.name == field).map(|f| f.ty.clone());
                    }
                }
                None
            }
            AssignTarget::Index { base, .. } => {
                if let Some(Type::List(inner)) = self.env.get(base) {
                    Some(*inner.clone())
                } else {
                    None
                }
            }
        }
    }

    fn fmt_target(&self, target: &AssignTarget) -> String {
        match target {
            AssignTarget::Var(v) => v.clone(),
            AssignTarget::Field { base, field } => format!("{}.{}", base, field),
            AssignTarget::Index { base, index } => {
                format!("{}[{}]", base, self.fmt_lua_index(index))
            }
        }
    }

    /// 0-based Hub index -> 1-based Lua index (`0` -> `1`, `i` -> `i + 1`).
    fn fmt_lua_index(&self, index: &Expr) -> String {
        if let Expr::Int(n) = index {
            if *n >= 0 {
                return format!("{}", n + 1);
            }
        }
        let inner = self.fmt_expr(index);
        if needs_parens(index, BinOp::Add, false) || matches!(index, Expr::Unary { .. }) {
            format!("({}) + 1", inner)
        } else {
            format!("{} + 1", inner)
        }
    }

    /// Half-open Hub range end `start..end` -> inclusive Lua range upper bound (`0..5` -> `0, 4`, `0..n` -> `0, n - 1`).
    fn fmt_lua_range_hi(&self, end: &Expr) -> String {
        if let Expr::Int(n) = end {
            if *n >= 1 {
                return format!("{}", n - 1);
            }
        }
        let inner = self.fmt_expr(end);
        if needs_parens(end, BinOp::Sub, false) || matches!(end, Expr::Unary { .. }) {
            format!("({}) - 1", inner)
        } else {
            format!("{} - 1", inner)
        }
    }

    fn fmt_pat(&self, pat: &MatchPat) -> String {
        match pat {
            MatchPat::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
            MatchPat::Int(v) => v.to_string(),
            MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
            MatchPat::Wildcard => "_".to_string(),
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
                if text.is_empty() {
                    out.push_str(&format!("{}--\n", pad));
                } else {
                    out.push_str(&format!("{}-- {}\n", pad, text));
                }
            }
            Stmt::Let {
                name, ty, value, ..
            } => {
                if let Some(t) = ty {
                    out.push_str(&format!("{}---@type {}\n", pad, self.fmt_type(t)));
                }
                let val_str = self.fmt_expr(value);
                out.push_str(&format!("{}local {} = {}\n", pad, name, val_str));
                let resolved_ty = ty
                    .clone()
                    .or_else(|| self.expr_type(value))
                    .or_else(|| list_hints.get(name).cloned());
                if let Some(t) = resolved_ty {
                    self.env.insert(name.clone(), t);
                }
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let tgt_str = self.fmt_target(target);
                match op {
                    AssignOp::Set => {
                        let val_str = self.fmt_expr(value);
                        let collides_with_compound = match value {
                            Expr::Binary {
                                op: BinOp::Add | BinOp::Sub,
                                left,
                                ..
                            } => expr_matches_target(left, target),
                            _ => false,
                        };
                        if collides_with_compound {
                            out.push_str(&format!("{}{} = {} -- @star-set\n", pad, tgt_str, val_str));
                        } else {
                            out.push_str(&format!("{}{} = {}\n", pad, tgt_str, val_str));
                        }
                    }
                    AssignOp::AddAssign => {
                        let is_str = self.target_type(target) == Some(Type::Str)
                            || self.expr_type(value) == Some(Type::Str);
                        let sep = if is_str { ".." } else { "+" };
                        let rhs = if needs_parens(value, BinOp::Add, true) {
                            format!("({})", self.fmt_expr(value))
                        } else {
                            self.fmt_expr(value)
                        };
                        out.push_str(&format!("{}{} = {} {} {}\n", pad, tgt_str, tgt_str, sep, rhs));
                    }
                    AssignOp::SubAssign => {
                        let rhs = if needs_parens(value, BinOp::Sub, true)
                            || matches!(value, Expr::Unary { op: UnaryOp::Neg, .. })
                        {
                            format!("({})", self.fmt_expr(value))
                        } else {
                            self.fmt_expr(value)
                        };
                        out.push_str(&format!("{}{} = {} - {}\n", pad, tgt_str, tgt_str, rhs));
                    }
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.fmt_if_chain(cond, then_body, else_body, indent, true, list_hints, out);
            }
            Stmt::Match { expr, arms, .. } => {
                out.push_str(&format!("{}do -- @star-match\n", pad));
                let inner_pad = "    ".repeat(indent + 1);
                out.push_str(&format!(
                    "{}local __star_m = {}\n",
                    inner_pad,
                    self.fmt_expr(expr)
                ));
                for (idx, arm) in arms.iter().enumerate() {
                    let is_last = idx + 1 == arms.len();
                    if arm.pat == MatchPat::Wildcard {
                        if idx == 0 {
                            out.push_str(&format!("{}if true then\n", inner_pad));
                        } else if is_last {
                            out.push_str(&format!("{}else\n", inner_pad));
                        } else {
                            out.push_str(&format!("{}elseif true then\n", inner_pad));
                        }
                    } else {
                        let kw = if idx == 0 { "if" } else { "elseif" };
                        out.push_str(&format!(
                            "{}{} __star_m == {} then\n",
                            inner_pad,
                            kw,
                            self.fmt_pat(&arm.pat)
                        ));
                    }
                    let saved = self.env.clone();
                    for s in &arm.body {
                        self.fmt_stmt(s, indent + 2, list_hints, out);
                    }
                    self.env = saved;
                }
                if !arms.is_empty() {
                    out.push_str(&format!("{}end\n", inner_pad));
                }
                out.push_str(&format!("{}end\n", pad));
            }
            Stmt::While { cond, body, .. } => {
                out.push_str(&format!("{}while {} do\n", pad, self.fmt_expr(cond)));
                self.loop_depth += 1;
                let depth = self.loop_depth;
                let saved = self.env.clone();
                for s in body {
                    self.fmt_stmt(s, indent + 1, list_hints, out);
                }
                self.env = saved;
                if block_has_direct_continue(body) {
                    out.push_str(&format!("{}    ::__star_cont_{}::\n", pad, depth));
                }
                self.loop_depth -= 1;
                out.push_str(&format!("{}end\n", pad));
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let elem_ty = match self.expr_type(iter) {
                    Some(Type::List(inner)) => Some(*inner),
                    _ => None,
                };
                out.push_str(&format!(
                    "{}for _, {} in ipairs({}) do\n",
                    pad,
                    var,
                    self.fmt_expr(iter)
                ));
                self.loop_depth += 1;
                let depth = self.loop_depth;
                let saved = self.env.clone();
                if let Some(et) = elem_ty {
                    self.env.insert(var.clone(), et);
                }
                for s in body {
                    self.fmt_stmt(s, indent + 1, list_hints, out);
                }
                self.env = saved;
                if block_has_direct_continue(body) {
                    out.push_str(&format!("{}    ::__star_cont_{}::\n", pad, depth));
                }
                self.loop_depth -= 1;
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
                    "{}for {} = {}, {} do\n",
                    pad,
                    var,
                    self.fmt_expr(start),
                    self.fmt_lua_range_hi(end)
                ));
                self.loop_depth += 1;
                let depth = self.loop_depth;
                let saved = self.env.clone();
                self.env.insert(var.clone(), Type::Int);
                for s in body {
                    self.fmt_stmt(s, indent + 1, list_hints, out);
                }
                self.env = saved;
                if block_has_direct_continue(body) {
                    out.push_str(&format!("{}    ::__star_cont_{}::\n", pad, depth));
                }
                self.loop_depth -= 1;
                out.push_str(&format!("{}end\n", pad));
            }
            Stmt::Break { .. } => {
                out.push_str(&format!("{}break\n", pad));
            }
            Stmt::Continue { .. } => {
                let d = self.loop_depth.max(1);
                out.push_str(&format!("{}goto __star_cont_{}\n", pad, d));
            }
            Stmt::Return { value, .. } => match value {
                Some(v) => out.push_str(&format!("{}return {}\n", pad, self.fmt_expr(v))),
                None => out.push_str(&format!("{}return\n", pad)),
            },
            Stmt::Assert { cond, .. } => {
                out.push_str(&format!("{}assert({})\n", pad, self.fmt_expr(cond)));
            }
            Stmt::AssertEq { left, right, .. } => {
                out.push_str(&format!(
                    "{}star_assert_eq({}, {})\n",
                    pad,
                    self.fmt_expr(left),
                    self.fmt_expr(right)
                ));
            }
            Stmt::Expr { expr, .. } => {
                out.push_str(&format!("{}{}\n", pad, self.fmt_expr(expr)));
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
        list_hints: &HashMap<String, Type>,
        out: &mut String,
    ) {
        let pad = "    ".repeat(indent);
        if first {
            out.push_str(&format!("{}if {} then\n", pad, self.fmt_expr(cond)));
        } else {
            out.push_str(&format!("{}elseif {} then\n", pad, self.fmt_expr(cond)));
        }
        let saved = self.env.clone();
        for s in then_body {
            self.fmt_stmt(s, indent + 1, list_hints, out);
        }
        self.env = saved;

        if else_body.len() == 1 {
            if let Stmt::If {
                cond: c2,
                then_body: t2,
                else_body: e2,
                ..
            } = &else_body[0]
            {
                self.fmt_if_chain(c2, t2, e2, indent, false, list_hints, out);
                return;
            }
        }

        if !else_body.is_empty() {
            out.push_str(&format!("{}else\n", pad));
            let saved_else = self.env.clone();
            for s in else_body {
                self.fmt_stmt(s, indent + 1, list_hints, out);
            }
            self.env = saved_else;
        }
        out.push_str(&format!("{}end\n", pad));
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
                if items.is_empty() {
                    "{}".to_string()
                } else {
                    let inner: Vec<String> = items.iter().map(|e| self.fmt_expr(e)).collect();
                    format!("{{ {} }}", inner.join(", "))
                }
            }
            Expr::StructInit { name, fields } => {
                if fields.is_empty() {
                    format!("{}.new({{}})", name)
                } else {
                    let inner: Vec<String> = fields
                        .iter()
                        .map(|(k, v)| format!("{} = {}", k, self.fmt_expr(v)))
                        .collect();
                    format!("{}.new({{ {} }})", name, inner.join(", "))
                }
            }
            Expr::FieldAccess { base, field } => {
                let b = if matches!(base.as_ref(), Expr::Binary { .. } | Expr::Unary { .. }) {
                    format!("({})", self.fmt_expr(base))
                } else {
                    self.fmt_expr(base)
                };
                format!("{}.{}", b, field)
            }
            Expr::Index { base, index } => {
                let b = if matches!(base.as_ref(), Expr::Binary { .. } | Expr::Unary { .. }) {
                    format!("({})", self.fmt_expr(base))
                } else {
                    self.fmt_expr(base)
                };
                format!("{}[{}]", b, self.fmt_lua_index(index))
            }
            Expr::Unary { op, expr: inner } => match op {
                UnaryOp::Neg => {
                    let s = self.fmt_expr(inner);
                    if matches!(
                        inner.as_ref(),
                        Expr::Binary { .. } | Expr::Unary { .. } | Expr::Intrinsic(_)
                    ) || s.starts_with('-')
                    {
                        format!("-({})", s)
                    } else {
                        format!("-{}", s)
                    }
                }
                UnaryOp::Not => {
                    let s = self.fmt_expr(inner);
                    if matches!(inner.as_ref(), Expr::Binary { .. } | Expr::Unary { .. }) {
                        format!("not ({})", s)
                    } else {
                        format!("not {}", s)
                    }
                }
            },
            Expr::Binary { op, left, right } => {
                match op {
                    BinOp::IntDiv => {
                        return format!(
                            "star_idiv({}, {})",
                            self.fmt_expr(left),
                            self.fmt_expr(right)
                        );
                    }
                    BinOp::Mod => {
                        return format!(
                            "star_irem({}, {})",
                            self.fmt_expr(left),
                            self.fmt_expr(right)
                        );
                    }
                    BinOp::Eq | BinOp::Ne => {
                        let deep = self
                            .expr_type(left)
                            .map(|t| self.is_deep_eq_type(&t))
                            .unwrap_or(false)
                            || self
                                .expr_type(right)
                                .map(|t| self.is_deep_eq_type(&t))
                                .unwrap_or(false);
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
                    _ => {}
                }

                let is_str_concat = *op == BinOp::Add
                    && (self.expr_type(left) == Some(Type::Str)
                        || self.expr_type(right) == Some(Type::Str));

                let op_str = if is_str_concat {
                    ".."
                } else {
                    match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        BinOp::Mul => "*",
                        BinOp::Div => "/",
                        BinOp::IntDiv | BinOp::Mod => unreachable!(),
                        BinOp::Eq => "==",
                        BinOp::Ne => "~=",
                        BinOp::Lt => "<",
                        BinOp::Le => "<=",
                        BinOp::Gt => ">",
                        BinOp::Ge => ">=",
                        BinOp::And => "and",
                        BinOp::Or => "or",
                    }
                };

                let lhs = if needs_parens(left, *op, false) {
                    format!("({})", self.fmt_expr(left))
                } else {
                    self.fmt_expr(left)
                };

                let rhs_raw = self.fmt_expr(right);
                let rhs_needs_wrap = needs_parens(right, *op, true)
                    || (*op == BinOp::Sub && rhs_raw.starts_with('-'));
                let rhs = if rhs_needs_wrap {
                    format!("({})", rhs_raw)
                } else {
                    rhs_raw
                };

                format!("{} {} {}", lhs, op_str, rhs)
            }
            Expr::Call { func, args } => {
                let inner: Vec<String> = args.iter().map(|a| self.fmt_expr(a)).collect();
                format!("{}({})", func, inner.join(", "))
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(x) => {
                    if matches!(
                        x,
                        Expr::Var(_)
                            | Expr::FieldAccess { .. }
                            | Expr::Index { .. }
                            | Expr::Call { .. }
                    ) {
                        format!("#{}", self.fmt_expr(x))
                    } else {
                        format!("#({})", self.fmt_expr(x))
                    }
                }
                Intrinsic::Min(a, b) => {
                    format!("math.min({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Max(a, b) => {
                    format!("math.max({}, {})", self.fmt_expr(a), self.fmt_expr(b))
                }
                Intrinsic::Abs(a) => format!("math.abs({})", self.fmt_expr(a)),
                Intrinsic::Push { list, value } => {
                    format!("table.insert({}, {})", self.fmt_expr(list), self.fmt_expr(value))
                }
                Intrinsic::Print(args) => {
                    let inner: Vec<String> = args.iter().map(|a| self.fmt_expr(a)).collect();
                    format!("star_print({})", inner.join(", "))
                }
                Intrinsic::Contains { haystack, needle } => {
                    format!(
                        "star_contains({}, {})",
                        self.fmt_expr(haystack),
                        self.fmt_expr(needle)
                    )
                }
                Intrinsic::Upper(s) => format!("string.upper({})", self.fmt_expr(s)),
                Intrinsic::Lower(s) => format!("string.lower({})", self.fmt_expr(s)),
                Intrinsic::ToStr(x) => format!("star_tostr({})", self.fmt_expr(x)),
            },
        }
    }
}

fn block_has_direct_continue(stmts: &[Stmt]) -> bool {
    for s in stmts {
        match s {
            Stmt::Continue { .. } => return true,
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                if block_has_direct_continue(then_body) || block_has_direct_continue(else_body) {
                    return true;
                }
            }
            Stmt::Match { arms, .. } => {
                if arms.iter().any(|a| block_has_direct_continue(&a.body)) {
                    return true;
                }
            }
            Stmt::While { .. } | Stmt::ForEach { .. } | Stmt::ForRange { .. } => {}
            _ => {}
        }
    }
    false
}

fn expr_matches_target(expr: &Expr, target: &AssignTarget) -> bool {
    match (expr, target) {
        (Expr::Var(ev), AssignTarget::Var(tv)) => ev == tv,
        (
            Expr::FieldAccess { base, field: ef },
            AssignTarget::Field {
                base: tb,
                field: tf,
            },
        ) => {
            if let Expr::Var(bv) = base.as_ref() {
                bv == tb && ef == tf
            } else {
                false
            }
        }
        (
            Expr::Index { base, index: ei },
            AssignTarget::Index {
                base: tb,
                index: ti,
            },
        ) => {
            if let Expr::Var(bv) = base.as_ref() {
                bv == tb && ei.as_ref() == ti
            } else {
                false
            }
        }
        _ => false,
    }
}

// ============================================================================
// Lexer & Recursive-Descent Parser (`put`) for Lua / LuaJIT + LuaCATS
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
enum LTokKind {
    Ident(String),
    Int(i64),
    Float(f64),
    Str(String),
    Comment(String),
    LuaCats(String),
    Directive(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semi,
    Dot,
    DotDot,
    DotDotDot,
    Colon,
    ColonColon,
    Plus,
    Minus,
    Star,
    Slash,
    SlashSlash,
    Percent,
    Hash,
    Eq,
    EqEq,
    TildeEq,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone)]
struct LTok {
    kind: LTokKind,
    line: usize,
    col: usize,
}

fn lex_lua(source: &str) -> Result<Vec<LTok>, Diagnostic> {
    let chars: Vec<char> = source.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut line = 1usize;
    let mut col = 1usize;
    let mut raw_tokens = Vec::new();
    let mut skip_until_preamble_end = false;

    if source.starts_with("-- StarLang Lua / LuaJIT + LuaCATS Runtime Helpers")
        && source.contains("-- @star-end-preamble")
    {
        skip_until_preamble_end = true;
    }

    while i < n {
        let ch = chars[i];
        if ch == '\n' {
            i += 1;
            line += 1;
            col = 1;
            continue;
        }
        if ch.is_ascii_whitespace() {
            i += 1;
            col += 1;
            continue;
        }

        let start_line = line;
        let start_col = col;

        // Comments: `--[[ ... ]]`, `---@...`, `-- @star-...`, `-- ...`
        if ch == '-' && i + 1 < n && chars[i + 1] == '-' {
            // Long block comment `--[[ ... ]]`
            if i + 3 < n && chars[i + 2] == '[' && chars[i + 3] == '[' {
                i += 4;
                col += 4;
                while i + 1 < n && !(chars[i] == ']' && chars[i + 1] == ']') {
                    if chars[i] == '\n' {
                        line += 1;
                        col = 1;
                    } else {
                        col += 1;
                    }
                    i += 1;
                }
                if i + 1 < n {
                    i += 2;
                    col += 2;
                }
                continue;
            }

            i += 2;
            col += 2;
            let text_start = i;
            while i < n && chars[i] != '\n' {
                i += 1;
                col += 1;
            }
            let raw_comment: String = chars[text_start..i].iter().collect();
            let trimmed = raw_comment.trim_end_matches('\r');

            if trimmed.trim() == "@star-end-preamble" {
                skip_until_preamble_end = false;
                continue;
            }
            if skip_until_preamble_end {
                continue;
            }

            if let Some(cats) = trimmed.strip_prefix("-@") {
                raw_tokens.push(LTok {
                    kind: LTokKind::LuaCats(cats.trim().to_string()),
                    line: start_line,
                    col: start_col,
                });
            } else if let Some(dir) = trimmed.trim().strip_prefix("@star-") {
                raw_tokens.push(LTok {
                    kind: LTokKind::Directive(dir.trim().to_string()),
                    line: start_line,
                    col: start_col,
                });
            } else {
                let clean = trimmed.strip_prefix(' ').unwrap_or(trimmed).to_string();
                raw_tokens.push(LTok {
                    kind: LTokKind::Comment(clean),
                    line: start_line,
                    col: start_col,
                });
            }
            continue;
        }

        if skip_until_preamble_end {
            i += 1;
            col += 1;
            continue;
        }

        // String literals `"..."` or `'...'`
        if ch == '"' || ch == '\'' {
            let quote = ch;
            i += 1;
            col += 1;
            let mut raw = String::new();
            let mut closed = false;
            while i < n {
                let c = chars[i];
                if c == '\\' && i + 1 < n {
                    raw.push(c);
                    raw.push(chars[i + 1]);
                    i += 2;
                    col += 2;
                    continue;
                }
                if c == quote {
                    i += 1;
                    col += 1;
                    closed = true;
                    break;
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
                    "lua",
                    "unterminated string literal",
                    start_line,
                    start_col,
                ));
            }
            raw_tokens.push(LTok {
                kind: LTokKind::Str(unescape_string(&raw)),
                line: start_line,
                col: start_col,
            });
            continue;
        }

        // Numbers (integers & floats)
        if ch.is_ascii_digit() {
            let num_start = i;
            let mut is_float = false;
            while i < n && chars[i].is_ascii_digit() {
                i += 1;
                col += 1;
            }
            if i < n
                && chars[i] == '.'
                && (i + 1 >= n || chars[i + 1] != '.')
                && i + 1 < n
                && chars[i + 1].is_ascii_digit()
            {
                is_float = true;
                i += 1;
                col += 1;
                while i < n && chars[i].is_ascii_digit() {
                    i += 1;
                    col += 1;
                }
            }
            if i < n && (chars[i] == 'e' || chars[i] == 'E') {
                is_float = true;
                i += 1;
                col += 1;
                if i < n && (chars[i] == '+' || chars[i] == '-') {
                    i += 1;
                    col += 1;
                }
                while i < n && chars[i].is_ascii_digit() {
                    i += 1;
                    col += 1;
                }
            }
            let text: String = chars[num_start..i].iter().collect();
            if is_float {
                let v = text.parse::<f64>().map_err(|_| {
                    Diagnostic::new("lua", format!("invalid float '{}'", text), start_line, start_col)
                })?;
                raw_tokens.push(LTok {
                    kind: LTokKind::Float(v),
                    line: start_line,
                    col: start_col,
                });
            } else {
                let v = text.parse::<i64>().map_err(|_| {
                    Diagnostic::new(
                        "lua",
                        format!("invalid integer '{}'", text),
                        start_line,
                        start_col,
                    )
                })?;
                raw_tokens.push(LTok {
                    kind: LTokKind::Int(v),
                    line: start_line,
                    col: start_col,
                });
            }
            continue;
        }

        // Identifiers / keywords
        if ch.is_ascii_alphabetic() || ch == '_' {
            let id_start = i;
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
                col += 1;
            }
            let ident: String = chars[id_start..i].iter().collect();
            raw_tokens.push(LTok {
                kind: LTokKind::Ident(ident),
                line: start_line,
                col: start_col,
            });
            continue;
        }

        // Multi-char operators & punctuation
        let two = if i + 1 < n {
            Some((ch, chars[i + 1]))
        } else {
            None
        };
        if ch == '.' && i + 2 < n && chars[i + 1] == '.' && chars[i + 2] == '.' {
            raw_tokens.push(LTok {
                kind: LTokKind::DotDotDot,
                line: start_line,
                col: start_col,
            });
            i += 3;
            col += 3;
            continue;
        }
        if let Some((a, b)) = two {
            let multi = match (a, b) {
                ('.', '.') => Some(LTokKind::DotDot),
                (':', ':') => Some(LTokKind::ColonColon),
                ('=', '=') => Some(LTokKind::EqEq),
                ('~', '=') | ('!', '=') => Some(LTokKind::TildeEq),
                ('<', '=') => Some(LTokKind::Le),
                ('>', '=') => Some(LTokKind::Ge),
                ('/', '/') => Some(LTokKind::SlashSlash),
                _ => None,
            };
            if let Some(kind) = multi {
                raw_tokens.push(LTok {
                    kind,
                    line: start_line,
                    col: start_col,
                });
                i += 2;
                col += 2;
                continue;
            }
        }

        let single = match ch {
            '(' => LTokKind::LParen,
            ')' => LTokKind::RParen,
            '{' => LTokKind::LBrace,
            '}' => LTokKind::RBrace,
            '[' => LTokKind::LBracket,
            ']' => LTokKind::RBracket,
            ',' => LTokKind::Comma,
            ';' => LTokKind::Semi,
            '.' => LTokKind::Dot,
            ':' => LTokKind::Colon,
            '+' => LTokKind::Plus,
            '-' => LTokKind::Minus,
            '*' => LTokKind::Star,
            '/' => LTokKind::Slash,
            '%' => LTokKind::Percent,
            '#' => LTokKind::Hash,
            '=' => LTokKind::Eq,
            '<' => LTokKind::Lt,
            '>' => LTokKind::Gt,
            other => {
                return Err(Diagnostic::new(
                    "lua",
                    format!("unexpected character '{}'", other),
                    start_line,
                    start_col,
                ));
            }
        };
        raw_tokens.push(LTok {
            kind: single,
            line: start_line,
            col: start_col,
        });
        i += 1;
        col += 1;
    }

    Ok(raw_tokens)
}

fn parse_luacats_type_str(raw: &str) -> Result<Type, String> {
    let s = raw.trim();
    if let Some(inner) = s.strip_suffix("[]") {
        let elem = parse_luacats_type_str(inner)?;
        return Ok(Type::List(Box::new(elem)));
    }
    match s {
        "integer" | "int" | "i64" => Ok(Type::Int),
        "number" | "float" | "f64" => Ok(Type::Float),
        "boolean" | "bool" => Ok(Type::Bool),
        "string" | "str" => Ok(Type::Str),
        "nil" | "void" => Ok(Type::Void),
        other if !other.is_empty()
            && other
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_') =>
        {
            Ok(Type::Named(other.to_string()))
        }
        other => Err(format!("unknown LuaCATS type '{}'", other)),
    }
}

fn prescan_lua_types(
    tokens: &[LTok],
    known_structs: &mut HashMap<String, Vec<String>>,
    known_enums: &mut HashSet<String>,
) {
    let mut cur_class: Option<String> = None;
    for tok in tokens {
        if let LTokKind::LuaCats(cats) = &tok.kind {
            if let Some(rest) = cats.strip_prefix("enum ") {
                let name = rest.split_whitespace().next().unwrap_or("").to_string();
                if !name.is_empty() {
                    known_enums.insert(name);
                }
                cur_class = None;
            } else if let Some(rest) = cats.strip_prefix("class ") {
                let name = rest.split_whitespace().next().unwrap_or("").to_string();
                if !name.is_empty() {
                    known_structs.entry(name.clone()).or_default();
                    cur_class = Some(name);
                }
            } else if let Some(rest) = cats.strip_prefix("field ") {
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

struct LuaParser {
    tokens: Vec<LTok>,
    pos: usize,
    known_structs: HashMap<String, Vec<String>>,
    known_enums: HashSet<String>,
}

const HELPER_FN_NAMES: &[&str] = &[
    "star_idiv",
    "star_irem",
    "star_tostr",
    "star_print",
    "star_eql",
    "star_neql",
    "star_assert_eq",
    "star_contains",
];

impl LuaParser {
    fn peek(&self) -> Option<&LTok> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&LTokKind> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }

    fn peek_kind_at(&self, offset: usize) -> Option<&LTokKind> {
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
    }

    fn next(&mut self) -> Option<LTok> {
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
        Err(Diagnostic::new("lua", msg, line, col))
    }

    fn eat(&mut self, expected: &LTokKind) -> bool {
        if self.peek_kind() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn is_kw(&self, kw: &str) -> bool {
        matches!(self.peek_kind(), Some(LTokKind::Ident(s)) if s == kw)
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.is_kw(kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &LTokKind, label: &str) -> Result<(), Diagnostic> {
        if self.eat(expected) {
            Ok(())
        } else {
            self.err(format!("expected {}", label))
        }
    }

    fn expect_kw(&mut self, kw: &str) -> Result<(), Diagnostic> {
        if self.eat_kw(kw) {
            Ok(())
        } else {
            self.err(format!("expected '{}'", kw))
        }
    }

    fn expect_ident(&mut self) -> Result<String, Diagnostic> {
        match self.next() {
            Some(LTok {
                kind: LTokKind::Ident(s),
                ..
            }) => Ok(s),
            _ => self.err("expected identifier"),
        }
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut module = HubModule::new();
        let mut comments: Vec<String> = Vec::new();
        let mut cats_lines: Vec<(String, usize, usize)> = Vec::new();

        while let Some(tok) = self.peek().cloned() {
            match &tok.kind {
                LTokKind::Semi => {
                    self.next();
                }
                LTokKind::Comment(c) => {
                    self.next();
                    comments.push(c.clone());
                }
                LTokKind::LuaCats(c) => {
                    self.next();
                    cats_lines.push((c.clone(), tok.line, tok.col));
                }
                LTokKind::Directive(_) => {
                    self.next();
                }
                LTokKind::Ident(s) if s == "main" && self.peek_kind_at(1) == Some(&LTokKind::LParen) => {
                    // Trailing `main()` entrypoint call
                    self.next();
                    self.next();
                    self.expect(&LTokKind::RParen, "')' after main()")?;
                    comments.clear();
                    cats_lines.clear();
                }
                _ => {
                    let has_enum = cats_lines.iter().any(|(c, _, _)| c.starts_with("enum "));
                    let has_class = cats_lines.iter().any(|(c, _, _)| c.starts_with("class "));

                    if has_enum {
                        let e = self.parse_enum_decl(
                            std::mem::take(&mut comments),
                            &std::mem::take(&mut cats_lines),
                        )?;
                        self.known_enums.insert(e.name.clone());
                        module.items.push(Item::Enum(e));
                        continue;
                    }

                    if has_class {
                        let s = self.parse_struct_decl(
                            std::mem::take(&mut comments),
                            &std::mem::take(&mut cats_lines),
                        )?;
                        self.known_structs.insert(
                            s.name.clone(),
                            s.fields.iter().map(|f| f.name.clone()).collect(),
                        );
                        module.items.push(Item::Struct(s));
                        continue;
                    }

                    // `[local] function ...`
                    let is_local_fn = self.is_kw("local")
                        && matches!(self.peek_kind_at(1), Some(LTokKind::Ident(k)) if k == "function");
                    let is_global_fn = self.is_kw("function");

                    if is_local_fn || is_global_fn {
                        if is_local_fn {
                            self.next(); // `local`
                        }
                        self.next(); // `function`
                        let fname = self.expect_ident()?;

                        // Skip `<StructName>.new(o) return o end` constructor helper if seen standalone
                        if self.eat(&LTokKind::Dot) {
                            let _method = self.expect_ident()?;
                            self.skip_lua_function_tail()?;
                            comments.clear();
                            cats_lines.clear();
                            continue;
                        }

                        if HELPER_FN_NAMES.contains(&fname.as_str()) {
                            self.skip_lua_function_tail()?;
                            comments.clear();
                            cats_lines.clear();
                            continue;
                        }

                        let doc_comments = std::mem::take(&mut comments);
                        let fn_cats = std::mem::take(&mut cats_lines);

                        if let Some(test_name) = fname.strip_prefix("test_") {
                            self.expect(&LTokKind::LParen, "'('")?;
                            self.expect(&LTokKind::RParen, "')'")?;
                            let body = self.parse_block_until(&["end"])?;
                            self.expect_kw("end")?;
                            module.items.push(Item::Test(TestDecl {
                                id: 0,
                                name: test_name.to_string(),
                                body,
                                comments: doc_comments,
                                meta: Metadata::new(),
                            }));
                        } else {
                            let fdecl = self.parse_fn_tail(fname, doc_comments, &fn_cats)?;
                            module.items.push(Item::Function(fdecl));
                        }
                        continue;
                    }

                    // Unannotated `local Name = { Variant = 0, ... }` enum table
                    if self.is_kw("local")
                        && matches!(self.peek_kind_at(1), Some(LTokKind::Ident(_)))
                        && self.peek_kind_at(2) == Some(&LTokKind::Eq)
                        && self.peek_kind_at(3) == Some(&LTokKind::LBrace)
                    {
                        let e = self.parse_enum_decl(std::mem::take(&mut comments), &[])?;
                        self.known_enums.insert(e.name.clone());
                        module.items.push(Item::Enum(e));
                        continue;
                    }

                    return self.err("unexpected top-level token in Lua module");
                }
            }
        }

        Ok(module)
    }

    fn skip_lua_function_tail(&mut self) -> Result<(), Diagnostic> {
        self.expect(&LTokKind::LParen, "'('")?;
        while !self.eat(&LTokKind::RParen) {
            if self.next().is_none() {
                return self.err("unterminated parameter list");
            }
        }
        let mut depth = 1usize;
        while depth > 0 {
            let Some(tok) = self.next() else {
                return self.err("unterminated function body");
            };
            if let LTokKind::Ident(w) = &tok.kind {
                match w.as_str() {
                    "function" | "if" | "do" => depth += 1,
                    "end" => depth -= 1,
                    _ => {}
                }
            }
        }
        Ok(())
    }

    fn parse_enum_decl(
        &mut self,
        comments: Vec<String>,
        _cats: &[(String, usize, usize)],
    ) -> Result<EnumDecl, Diagnostic> {
        let _ = self.eat_kw("local");
        let name = self.expect_ident()?;
        self.expect(&LTokKind::Eq, "'=' after enum name")?;
        self.expect(&LTokKind::LBrace, "'{' starting enum table")?;
        let mut variants = Vec::new();
        while !self.eat(&LTokKind::RBrace) {
            if matches!(self.peek_kind(), Some(LTokKind::Comment(_)) | Some(LTokKind::LuaCats(_))) {
                self.next();
                continue;
            }
            let vname = self.expect_ident()?;
            self.expect(&LTokKind::Eq, "'=' after enum variant")?;
            let _ = self.eat(&LTokKind::Minus);
            match self.next() {
                Some(LTok {
                    kind: LTokKind::Int(_),
                    ..
                }) => {}
                _ => return self.err("expected integer discriminant in enum table"),
            }
            variants.push(vname);
            let _ = self.eat(&LTokKind::Comma) || self.eat(&LTokKind::Semi);
        }
        Ok(EnumDecl {
            id: 0,
            name,
            variants,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_struct_decl(
        &mut self,
        comments: Vec<String>,
        cats: &[(String, usize, usize)],
    ) -> Result<StructDecl, Diagnostic> {
        let mut class_name = String::new();
        let mut fields = Vec::new();

        for (c, line, col) in cats {
            if let Some(rest) = c.strip_prefix("class ") {
                class_name = rest.split_whitespace().next().unwrap_or("").to_string();
            } else if let Some(rest) = c.strip_prefix("field ") {
                let mut parts = rest.trim().splitn(2, char::is_whitespace);
                let fname = parts.next().unwrap_or("").trim().to_string();
                let ty_raw = parts.next().unwrap_or("").trim();
                let ty = parse_luacats_type_str(ty_raw)
                    .map_err(|m| Diagnostic::new("lua", m, *line, *col))?;
                fields.push(Field {
                    id: 0,
                    name: fname,
                    ty,
                    meta: Metadata::new(),
                });
            }
        }

        // Consume `local <Name> = {}`
        let _ = self.eat_kw("local");
        let tbl_name = self.expect_ident()?;
        if class_name.is_empty() {
            class_name = tbl_name;
        }
        self.expect(&LTokKind::Eq, "'=' after struct table")?;
        self.expect(&LTokKind::LBrace, "'{'")?;
        self.expect(&LTokKind::RBrace, "'}'")?;

        // Consume optional `function <Name>.new(o) return o end`
        let is_ctor = (self.is_kw("function")
            && matches!(self.peek_kind_at(1), Some(LTokKind::Ident(n)) if n == &class_name)
            && self.peek_kind_at(2) == Some(&LTokKind::Dot))
            || (self.is_kw("local")
                && matches!(self.peek_kind_at(1), Some(LTokKind::Ident(k)) if k == "function")
                && matches!(self.peek_kind_at(2), Some(LTokKind::Ident(n)) if n == &class_name));
        if is_ctor {
            let _ = self.eat_kw("local");
            let _ = self.eat_kw("function");
            let _ = self.expect_ident()?;
            let _ = self.eat(&LTokKind::Dot);
            let _ = self.expect_ident()?;
            self.skip_lua_function_tail()?;
        }

        Ok(StructDecl {
            id: 0,
            name: class_name,
            fields,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_fn_tail(
        &mut self,
        name: String,
        comments: Vec<String>,
        cats: &[(String, usize, usize)],
    ) -> Result<FnDecl, Diagnostic> {
        let mut param_types: HashMap<String, Type> = HashMap::new();
        let mut ret_ty = Type::Void;

        for (c, line, col) in cats {
            if let Some(rest) = c.strip_prefix("param ") {
                let mut parts = rest.trim().splitn(2, char::is_whitespace);
                let pname = parts.next().unwrap_or("").trim().to_string();
                let ty_raw = parts.next().unwrap_or("integer").trim();
                let ty = parse_luacats_type_str(ty_raw)
                    .map_err(|m| Diagnostic::new("lua", m, *line, *col))?;
                param_types.insert(pname, ty);
            } else if let Some(rest) = c.strip_prefix("return ") {
                let ty_raw = rest.trim();
                ret_ty = parse_luacats_type_str(ty_raw)
                    .map_err(|m| Diagnostic::new("lua", m, *line, *col))?;
            }
        }

        self.expect(&LTokKind::LParen, "'('")?;
        let mut params = Vec::new();
        if !self.eat(&LTokKind::RParen) {
            loop {
                let pname = self.expect_ident()?;
                let pty = param_types.remove(&pname).unwrap_or(Type::Int);
                params.push(Param {
                    id: 0,
                    name: pname,
                    ty: pty,
                    meta: Metadata::new(),
                });
                if !self.eat(&LTokKind::Comma) {
                    break;
                }
            }
            self.expect(&LTokKind::RParen, "')'")?;
        }

        let body = self.parse_block_until(&["end"])?;
        self.expect_kw("end")?;

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

    fn parse_block_until(&mut self, terminators: &[&str]) -> Result<Vec<Stmt>, Diagnostic> {
        let mut stmts = Vec::new();
        let mut pending_type: Option<Type> = None;

        while let Some(tok) = self.peek().cloned() {
            if let LTokKind::Ident(w) = &tok.kind {
                if terminators.contains(&w.as_str()) {
                    break;
                }
            }
            if self.eat(&LTokKind::Semi) {
                continue;
            }
            // Skip `::__star_cont_N::` labels emitted for `continue`
            if self.eat(&LTokKind::ColonColon) {
                let _ = self.expect_ident()?;
                self.expect(&LTokKind::ColonColon, "'::' closing label")?;
                continue;
            }
            if let LTokKind::LuaCats(cats) = &tok.kind {
                self.next();
                if let Some(rest) = cats.strip_prefix("type ") {
                    let ty = parse_luacats_type_str(rest.trim())
                        .map_err(|m| Diagnostic::new("lua", m, tok.line, tok.col))?;
                    pending_type = Some(ty);
                }
                continue;
            }
            if let LTokKind::Directive(_) = &tok.kind {
                self.next();
                continue;
            }
            if let LTokKind::Comment(c) = &tok.kind {
                self.next();
                stmts.push(Stmt::Comment {
                    id: 0,
                    text: c.clone(),
                });
                continue;
            }

            let stmt = self.parse_stmt(pending_type.take())?;
            stmts.push(stmt);
        }
        Ok(stmts)
    }

    fn parse_stmt(&mut self, pending_type: Option<Type>) -> Result<Stmt, Diagnostic> {
        if self.eat_kw("local") {
            let name = self.expect_ident()?;
            self.expect(&LTokKind::Eq, "'=' after local variable name")?;
            let value = self.parse_expr()?;
            return Ok(Stmt::Let {
                id: 0,
                name,
                mutable: false,
                ty: pending_type,
                value,
                meta: Metadata::new(),
            });
        }

        if self.eat_kw("if") {
            return self.parse_if_stmt();
        }

        if self.eat_kw("do") {
            if matches!(self.peek_kind(), Some(LTokKind::Directive(d)) if d == "match") {
                self.next();
                return self.parse_match_block();
            }
            let inner = self.parse_block_until(&["end"])?;
            self.expect_kw("end")?;
            if inner.len() == 1 {
                return Ok(inner.into_iter().next().unwrap());
            }
            return self.err("unsupported standalone `do ... end` block with multiple statements");
        }

        if self.eat_kw("while") {
            let cond = self.parse_expr()?;
            self.expect_kw("do")?;
            let body = self.parse_block_until(&["end"])?;
            self.expect_kw("end")?;
            return Ok(Stmt::While {
                id: 0,
                cond,
                body,
                meta: Metadata::new(),
            });
        }

        if self.eat_kw("for") {
            return self.parse_for_stmt();
        }

        if self.eat_kw("break") {
            return Ok(Stmt::Break { id: 0 });
        }

        if self.eat_kw("continue") {
            return Ok(Stmt::Continue { id: 0 });
        }

        if self.eat_kw("goto") {
            let lbl = self.expect_ident()?;
            if lbl.starts_with("__star_cont") {
                return Ok(Stmt::Continue { id: 0 });
            }
            return self.err(format!("unsupported goto label '{}'", lbl));
        }

        if self.eat_kw("return") {
            let is_end = match self.peek_kind() {
                None | Some(LTokKind::Semi) | Some(LTokKind::ColonColon) => true,
                Some(LTokKind::Ident(w))
                    if matches!(w.as_str(), "end" | "else" | "elseif") =>
                {
                    true
                }
                _ => false,
            };
            if is_end {
                return Ok(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                });
            }
            let val = self.parse_expr()?;
            return Ok(Stmt::Return {
                id: 0,
                value: Some(val),
                meta: Metadata::new(),
            });
        }

        if self.is_kw("assert") && self.peek_kind_at(1) == Some(&LTokKind::LParen) {
            self.next();
            self.next();
            let cond = self.parse_expr()?;
            if self.eat(&LTokKind::Comma) {
                let _ = self.parse_expr()?;
            }
            self.expect(&LTokKind::RParen, "')' after assert")?;
            return Ok(Stmt::Assert {
                id: 0,
                cond,
                meta: Metadata::new(),
            });
        }

        if self.is_kw("star_assert_eq") && self.peek_kind_at(1) == Some(&LTokKind::LParen) {
            self.next();
            self.next();
            let left = self.parse_expr()?;
            self.expect(&LTokKind::Comma, "',' in star_assert_eq")?;
            let right = self.parse_expr()?;
            self.expect(&LTokKind::RParen, "')' after star_assert_eq")?;
            return Ok(Stmt::AssertEq {
                id: 0,
                left,
                right,
                meta: Metadata::new(),
            });
        }

        // Assignment or expression statement
        let lhs = self.parse_expr()?;
        if self.eat(&LTokKind::Eq) {
            let target = expr_to_assign_target(lhs)
                .ok_or_else(|| Diagnostic::new("lua", "invalid assignment target", 1, 1))?;
            let rhs = self.parse_expr()?;
            let force_set = if matches!(self.peek_kind(), Some(LTokKind::Directive(d)) if d == "set")
            {
                self.next();
                true
            } else {
                false
            };

            if !force_set {
                if let Expr::Binary { op, left, right } = &rhs {
                    if expr_matches_target(left, &target) {
                        if *op == BinOp::Add {
                            return Ok(Stmt::Assign {
                                id: 0,
                                target,
                                op: AssignOp::AddAssign,
                                value: (*right.clone()),
                                meta: Metadata::new(),
                            });
                        } else if *op == BinOp::Sub {
                            return Ok(Stmt::Assign {
                                id: 0,
                                target,
                                op: AssignOp::SubAssign,
                                value: (*right.clone()),
                                meta: Metadata::new(),
                            });
                        }
                    }
                }
            }

            return Ok(Stmt::Assign {
                id: 0,
                target,
                op: AssignOp::Set,
                value: rhs,
                meta: Metadata::new(),
            });
        }

        Ok(Stmt::Expr {
            id: 0,
            expr: lhs,
            meta: Metadata::new(),
        })
    }

    fn parse_if_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        let cond = self.parse_expr()?;
        self.expect_kw("then")?;
        let then_body = self.parse_block_until(&["elseif", "else", "end"])?;
        let else_body = if self.eat_kw("elseif") {
            vec![self.parse_if_stmt()?]
        } else if self.eat_kw("else") {
            let b = self.parse_block_until(&["end"])?;
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

    fn parse_match_block(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect_kw("local")?;
        let tmp = self.expect_ident()?;
        self.expect(&LTokKind::Eq, "'='")?;
        let scrutinee = self.parse_expr()?;
        let mut arms = Vec::new();

        if self.eat_kw("if") {
            loop {
                let pat = self.parse_match_cond(&tmp)?;
                self.expect_kw("then")?;
                let body = self.parse_block_until(&["elseif", "else", "end"])?;
                arms.push(MatchArm { pat, body });

                if self.eat_kw("elseif") {
                    continue;
                }
                if self.eat_kw("else") {
                    let body = self.parse_block_until(&["end"])?;
                    arms.push(MatchArm {
                        pat: MatchPat::Wildcard,
                        body,
                    });
                }
                self.expect_kw("end")?;
                break;
            }
        }

        self.expect_kw("end")?;
        Ok(Stmt::Match {
            id: 0,
            expr: scrutinee,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_match_cond(&mut self, tmp: &str) -> Result<MatchPat, Diagnostic> {
        if self.eat_kw("true") {
            return Ok(MatchPat::Wildcard);
        }
        let lhs = self.expect_ident()?;
        if lhs != tmp {
            return self.err("expected match scrutinee variable");
        }
        self.expect(&LTokKind::EqEq, "'==' in match arm")?;
        if self.eat(&LTokKind::Minus) {
            match self.next() {
                Some(LTok {
                    kind: LTokKind::Int(v),
                    ..
                }) => return Ok(MatchPat::Int(-v)),
                _ => return self.err("expected integer after '-' in match pattern"),
            }
        }
        match self.next() {
            Some(LTok {
                kind: LTokKind::Int(v),
                ..
            }) => Ok(MatchPat::Int(v)),
            Some(LTok {
                kind: LTokKind::Str(s),
                ..
            }) => Ok(MatchPat::Str(s)),
            Some(LTok {
                kind: LTokKind::Ident(ename),
                ..
            }) => {
                self.expect(&LTokKind::Dot, "'.' in enum pattern")?;
                let variant = self.expect_ident()?;
                Ok(MatchPat::EnumVariant {
                    enum_name: ename,
                    variant,
                })
            }
            _ => self.err("expected match pattern"),
        }
    }

    fn parse_for_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        let first = self.expect_ident()?;
        // `for _, x in ipairs(xs) do`
        if self.eat(&LTokKind::Comma) {
            let var = self.expect_ident()?;
            self.expect_kw("in")?;
            let iter = if self.eat_kw("ipairs") || self.eat_kw("pairs") {
                self.expect(&LTokKind::LParen, "'(' after ipairs")?;
                let it = self.parse_expr()?;
                self.expect(&LTokKind::RParen, "')' after ipairs")?;
                it
            } else {
                self.parse_expr()?
            };
            self.expect_kw("do")?;
            let body = self.parse_block_until(&["end"])?;
            self.expect_kw("end")?;
            return Ok(Stmt::ForEach {
                id: 0,
                var,
                iter,
                body,
                meta: Metadata::new(),
            });
        }

        // `for i = start, hi do` (inclusive Lua -> half-open Hub `start..end`)
        self.expect(&LTokKind::Eq, "'=' in numeric for loop")?;
        let start = self.parse_expr()?;
        self.expect(&LTokKind::Comma, "',' in numeric for loop")?;
        let raw_hi = self.parse_expr()?;
        if self.eat(&LTokKind::Comma) {
            let _step = self.parse_expr()?;
        }
        let end = unlift_lua_range_hi(raw_hi);
        self.expect_kw("do")?;
        let body = self.parse_block_until(&["end"])?;
        self.expect_kw("end")?;
        Ok(Stmt::ForRange {
            id: 0,
            var: first,
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
        let mut left = self.parse_cmp()?;
        while self.eat_kw("and") {
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
        let mut left = self.parse_concat()?;
        loop {
            let op = match self.peek_kind() {
                Some(LTokKind::EqEq) => Some(BinOp::Eq),
                Some(LTokKind::TildeEq) => Some(BinOp::Ne),
                Some(LTokKind::Lt) => Some(BinOp::Lt),
                Some(LTokKind::Le) => Some(BinOp::Le),
                Some(LTokKind::Gt) => Some(BinOp::Gt),
                Some(LTokKind::Ge) => Some(BinOp::Ge),
                _ => None,
            };
            if let Some(op) = op {
                self.next();
                let right = self.parse_concat()?;
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

    fn parse_concat(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_add()?;
        while self.eat(&LTokKind::DotDot) {
            let right = self.parse_add()?;
            left = Expr::Binary {
                op: BinOp::Add,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_add(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_mul()?;
        loop {
            let op = match self.peek_kind() {
                Some(LTokKind::Plus) => Some(BinOp::Add),
                Some(LTokKind::Minus) => Some(BinOp::Sub),
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
                Some(LTokKind::Star) => Some(BinOp::Mul),
                Some(LTokKind::Slash) => Some(BinOp::Div),
                Some(LTokKind::SlashSlash) => Some(BinOp::IntDiv),
                Some(LTokKind::Percent) => Some(BinOp::Mod),
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
        if self.eat(&LTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        if self.eat_kw("not") {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Not,
                expr: Box::new(inner),
            });
        }
        if self.eat(&LTokKind::Hash) {
            let inner = self.parse_unary()?;
            return Ok(Expr::intrinsic(Intrinsic::Len(inner)));
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut base = self.parse_primary()?;

        loop {
            if self.eat(&LTokKind::Dot) {
                let member = self.expect_ident()?;

                if let Expr::Var(ref name) = base {
                    // `StructName.new({ f = v, ... })`
                    if member == "new"
                        && self.known_structs.contains_key(name)
                        && self.peek_kind() == Some(&LTokKind::LParen)
                    {
                        let sname = name.clone();
                        self.next(); // `(`
                        let fields = self.parse_struct_fields()?;
                        self.expect(&LTokKind::RParen, "')' after Struct.new")?;
                        base = Expr::StructInit {
                            name: sname,
                            fields,
                        };
                        continue;
                    }

                    // Module-qualified stdlib intrinsics (`math.*`, `table.insert`, `string.*`)
                    if matches!(name.as_str(), "math" | "table" | "string")
                        && self.peek_kind() == Some(&LTokKind::LParen)
                    {
                        let mod_name = name.clone();
                        let args = self.parse_arg_list()?;
                        base = self.lower_stdlib_call(&mod_name, &member, args)?;
                        continue;
                    }

                    // `EnumName.Variant`
                    if self.known_enums.contains(name)
                        || (name.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false)
                            && member
                                .chars()
                                .next()
                                .map(|c| c.is_ascii_uppercase())
                                .unwrap_or(false)
                            && !self.known_structs.contains_key(name))
                    {
                        base = Expr::EnumVariant {
                            enum_name: name.clone(),
                            variant: member,
                        };
                        continue;
                    }
                }

                base = Expr::FieldAccess {
                    base: Box::new(base),
                    field: member,
                };
                continue;
            }

            if self.eat(&LTokKind::Colon) {
                let method = self.expect_ident()?;
                let _args = self.parse_arg_list()?;
                base = match method.as_str() {
                    "upper" => Expr::intrinsic(Intrinsic::Upper(base)),
                    "lower" => Expr::intrinsic(Intrinsic::Lower(base)),
                    _ => return self.err(format!("unsupported Lua method ':{}'", method)),
                };
                continue;
            }

            if self.eat(&LTokKind::LBracket) {
                let raw_idx = self.parse_expr()?;
                self.expect(&LTokKind::RBracket, "']'")?;
                base = Expr::Index {
                    base: Box::new(base),
                    index: Box::new(unlift_lua_index(raw_idx)),
                };
                continue;
            }

            if self.peek_kind() == Some(&LTokKind::LParen) {
                if let Expr::Var(fname) = base {
                    let args = self.parse_arg_list()?;
                    base = self.lower_fn_call(fname, args)?;
                    continue;
                } else {
                    return self.err("indirect call expressions are not supported");
                }
            }

            break;
        }

        Ok(base)
    }

    fn lower_stdlib_call(
        &self,
        mod_name: &str,
        member: &str,
        mut args: Vec<Expr>,
    ) -> Result<Expr, Diagnostic> {
        match (mod_name, member) {
            ("math", "min") if args.len() == 2 => {
                let b = args.pop().unwrap();
                let a = args.pop().unwrap();
                Ok(Expr::intrinsic(Intrinsic::Min(a, b)))
            }
            ("math", "max") if args.len() == 2 => {
                let b = args.pop().unwrap();
                let a = args.pop().unwrap();
                Ok(Expr::intrinsic(Intrinsic::Max(a, b)))
            }
            ("math", "abs") if args.len() == 1 => {
                Ok(Expr::intrinsic(Intrinsic::Abs(args.pop().unwrap())))
            }
            ("table", "insert") if args.len() == 2 => {
                let value = args.pop().unwrap();
                let list = args.pop().unwrap();
                Ok(Expr::intrinsic(Intrinsic::Push { list, value }))
            }
            ("string", "upper") if args.len() == 1 => {
                Ok(Expr::intrinsic(Intrinsic::Upper(args.pop().unwrap())))
            }
            ("string", "lower") if args.len() == 1 => {
                Ok(Expr::intrinsic(Intrinsic::Lower(args.pop().unwrap())))
            }
            ("string", "len") if args.len() == 1 => {
                Ok(Expr::intrinsic(Intrinsic::Len(args.pop().unwrap())))
            }
            _ => self.err(format!("unsupported Lua stdlib call '{}.{}'", mod_name, member)),
        }
    }

    fn lower_fn_call(&self, fname: String, mut args: Vec<Expr>) -> Result<Expr, Diagnostic> {
        match fname.as_str() {
            "star_idiv" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                Ok(Expr::Binary {
                    op: BinOp::IntDiv,
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            "star_irem" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                Ok(Expr::Binary {
                    op: BinOp::Mod,
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            "star_eql" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                Ok(Expr::Binary {
                    op: BinOp::Eq,
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            "star_neql" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                Ok(Expr::Binary {
                    op: BinOp::Ne,
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            "star_contains" if args.len() == 2 => {
                let needle = args.pop().unwrap();
                let haystack = args.pop().unwrap();
                Ok(Expr::intrinsic(Intrinsic::Contains { haystack, needle }))
            }
            "star_tostr" | "tostring" if args.len() == 1 => {
                Ok(Expr::intrinsic(Intrinsic::ToStr(args.pop().unwrap())))
            }
            "star_print" | "print" => Ok(Expr::intrinsic(Intrinsic::Print(args))),
            _ => Ok(Expr::Call { func: fname, args }),
        }
    }

    fn parse_arg_list(&mut self) -> Result<Vec<Expr>, Diagnostic> {
        self.expect(&LTokKind::LParen, "'('")?;
        let mut args = Vec::new();
        if !self.eat(&LTokKind::RParen) {
            loop {
                args.push(self.parse_expr()?);
                if !self.eat(&LTokKind::Comma) {
                    break;
                }
            }
            self.expect(&LTokKind::RParen, "')'")?;
        }
        Ok(args)
    }

    fn parse_struct_fields(&mut self) -> Result<Vec<(String, Expr)>, Diagnostic> {
        self.expect(&LTokKind::LBrace, "'{' in struct initializer")?;
        let mut fields = Vec::new();
        while !self.eat(&LTokKind::RBrace) {
            let fname = self.expect_ident()?;
            self.expect(&LTokKind::Eq, "'=' after struct field name")?;
            let val = self.parse_expr()?;
            fields.push((fname, val));
            if !(self.eat(&LTokKind::Comma) || self.eat(&LTokKind::Semi)) {
                self.expect(&LTokKind::RBrace, "'}' after struct fields")?;
                break;
            }
        }
        Ok(fields)
    }

    fn parse_primary(&mut self) -> Result<Expr, Diagnostic> {
        if self.eat(&LTokKind::LParen) {
            let inner = self.parse_expr()?;
            self.expect(&LTokKind::RParen, "')'")?;
            return Ok(inner);
        }

        if self.eat(&LTokKind::LBrace) {
            // Either list literal `{ e1, e2 }` or table record `{ f1 = v1, ... }`
            if self.eat(&LTokKind::RBrace) {
                return Ok(Expr::List(Vec::new()));
            }
            if matches!(self.peek_kind(), Some(LTokKind::Ident(_)))
                && self.peek_kind_at(1) == Some(&LTokKind::Eq)
            {
                let mut fields = Vec::new();
                while !self.eat(&LTokKind::RBrace) {
                    let fname = self.expect_ident()?;
                    self.expect(&LTokKind::Eq, "'='")?;
                    let val = self.parse_expr()?;
                    fields.push((fname, val));
                    if !(self.eat(&LTokKind::Comma) || self.eat(&LTokKind::Semi)) {
                        self.expect(&LTokKind::RBrace, "'}'")?;
                        break;
                    }
                }
                let fnames: Vec<&str> = fields.iter().map(|(k, _)| k.as_str()).collect();
                let mut struct_name = String::new();
                for (sname, sfields) in &self.known_structs {
                    if sfields.len() == fnames.len()
                        && sfields.iter().all(|sf| fnames.contains(&sf.as_str()))
                    {
                        struct_name = sname.clone();
                        break;
                    }
                }
                return Ok(Expr::StructInit {
                    name: struct_name,
                    fields,
                });
            }

            let mut items = Vec::new();
            while !self.eat(&LTokKind::RBrace) {
                items.push(self.parse_expr()?);
                if !(self.eat(&LTokKind::Comma) || self.eat(&LTokKind::Semi)) {
                    self.expect(&LTokKind::RBrace, "'}'")?;
                    break;
                }
            }
            return Ok(Expr::List(items));
        }

        match self.next() {
            Some(LTok {
                kind: LTokKind::Int(v),
                ..
            }) => Ok(Expr::Int(v)),
            Some(LTok {
                kind: LTokKind::Float(v),
                ..
            }) => Ok(Expr::Float(v)),
            Some(LTok {
                kind: LTokKind::Str(s),
                ..
            }) => Ok(Expr::Str(s)),
            Some(LTok {
                kind: LTokKind::Ident(s),
                ..
            }) => match s.as_str() {
                "true" => Ok(Expr::Bool(true)),
                "false" => Ok(Expr::Bool(false)),
                _ => Ok(Expr::Var(s)),
            },
            _ => self.err("expected expression in Lua source"),
        }
    }
}

/// 1-based Lua index -> 0-based Hub index (`1` -> `0`, `i + 1` -> `i`, hand-written `k` -> `k - 1`).
fn unlift_lua_index(raw: Expr) -> Expr {
    match raw {
        Expr::Int(k) if k >= 1 => Expr::Int(k - 1),
        Expr::Binary {
            op: BinOp::Add,
            left,
            right,
        } if *right == Expr::Int(1) => *left,
        other => Expr::Binary {
            op: BinOp::Sub,
            left: Box::new(other),
            right: Box::new(Expr::Int(1)),
        },
    }
}

/// Inclusive Lua numeric-for upper bound -> half-open Hub range end (`4` -> `5`, `n - 1` -> `n`, hand-written `n` -> `n + 1`).
fn unlift_lua_range_hi(raw: Expr) -> Expr {
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

use std::collections::{HashMap, HashSet};

use crate::hub::{
    infer_expr_type, AssignOp, AssignTarget, BinOp, Diagnostic, EnumDecl, Expr, Field, FnDecl,
    HubModule, Intrinsic, Item, MatchArm, MatchPat, Metadata, Param, Stmt, StructDecl, TestDecl,
    Type, UnaryOp,
};
use crate::lens::{escape_str, format_float, needs_parens, LanguageLens, SpokeId};
use crate::reconcile::reconcile_modules;
use crate::spokes::unescape_string;

pub struct ZigLens;

impl LanguageLens for ZigLens {
    fn id(&self) -> SpokeId {
        SpokeId::Zig
    }

    fn get(&self, hub: &HubModule) -> String {
        let mut fmt = ZigFormatter::new(hub);
        let usage = fmt.scan_usage(hub);
        let mut out = String::new();
        fmt.emit_module(hub, &usage, &mut out);
        out
    }

    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic> {
        let tokens = lex_zig(source)?;
        let (known_structs, known_enums) = prescan_zig_types(&tokens);
        let mut parser = ZigParser::new(&tokens, known_structs, known_enums);
        let parsed = parser.parse_module()?;
        Ok(reconcile_modules(parsed, prev_hub, SpokeId::Zig))
    }
}

#[derive(Default)]
struct ZigUsage {
    need_printf: bool,
    need_snprintf: bool,
    need_malloc: bool,
    need_list: bool,
    need_eql: bool,
    need_str_cmp: bool,
    need_str_concat: bool,
    need_str_contains: bool,
    need_upper: bool,
    need_lower: bool,
    need_to_str: bool,
    need_len: bool,
    need_abs: bool,
    need_println: bool,
}

struct ZigFormatter {
    fn_ret_types: HashMap<String, Type>,
    struct_fields: HashMap<String, HashMap<String, Type>>,
    enum_variants: HashMap<String, Vec<String>>,
    enum_names: HashSet<String>,
    local_env: HashMap<String, Type>,
}

impl ZigFormatter {
    fn new(hub: &HubModule) -> Self {
        let mut fn_ret_types = HashMap::new();
        let mut struct_fields = HashMap::new();
        let mut enum_variants = HashMap::new();
        let mut enum_names = HashSet::new();

        for item in &hub.items {
            match item {
                Item::Function(f) => {
                    fn_ret_types.insert(f.name.clone(), f.ret_ty.clone());
                }
                Item::Struct(s) => {
                    let mut m = HashMap::new();
                    for f in &s.fields {
                        m.insert(f.name.clone(), f.ty.clone());
                    }
                    struct_fields.insert(s.name.clone(), m);
                }
                Item::Enum(e) => {
                    enum_names.insert(e.name.clone());
                    enum_variants.insert(e.name.clone(), e.variants.clone());
                }
                Item::Test(_) => {}
            }
        }

        Self {
            fn_ret_types,
            struct_fields,
            enum_variants,
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

    fn target_ty(&self, target: &AssignTarget) -> Option<Type> {
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
        self.expr_ty(&target_expr)
    }

    fn fmt_type(ty: &Type) -> String {
        match ty {
            Type::Int => "i64".to_string(),
            Type::Float => "f64".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Str => "[]const u8".to_string(),
            Type::Void => "void".to_string(),
            Type::Named(n) => n.clone(),
            Type::List(inner) => format!("StarList({})", Self::fmt_type(inner)),
        }
    }

    fn type_has_list(ty: &Type) -> bool {
        matches!(ty, Type::List(_))
    }

    fn type_needs_deep_eql(&self, ty: &Type) -> bool {
        match ty {
            Type::Str | Type::List(_) => true,
            Type::Named(n) => !self.enum_names.contains(n),
            _ => false,
        }
    }

    fn scan_usage(&mut self, hub: &HubModule) -> ZigUsage {
        let mut u = ZigUsage::default();

        for item in &hub.items {
            match item {
                Item::Struct(s) => {
                    for f in &s.fields {
                        if Self::type_has_list(&f.ty) {
                            u.need_list = true;
                        }
                    }
                }
                Item::Enum(_) => {}
                Item::Function(f) => {
                    self.local_env.clear();
                    for p in &f.params {
                        if Self::type_has_list(&p.ty) {
                            u.need_list = true;
                        }
                        self.local_env.insert(p.name.clone(), p.ty.clone());
                    }
                    if Self::type_has_list(&f.ret_ty) {
                        u.need_list = true;
                    }
                    self.scan_stmts(&f.body, &mut u);
                }
                Item::Test(t) => {
                    self.local_env.clear();
                    self.scan_stmts(&t.body, &mut u);
                }
            }
        }

        if u.need_list {
            u.need_malloc = true;
            u.need_eql = true;
        }
        if u.need_str_concat || u.need_upper || u.need_lower {
            u.need_malloc = true;
        }
        if u.need_to_str {
            u.need_malloc = true;
            u.need_snprintf = true;
        }
        if u.need_println {
            u.need_printf = true;
        }

        u
    }

    fn scan_stmts(&mut self, stmts: &[Stmt], u: &mut ZigUsage) {
        for stmt in stmts {
            match stmt {
                Stmt::Let {
                    name, ty, value, ..
                } => {
                    self.scan_expr(value, u);
                    let resolved = ty.clone().or_else(|| self.expr_ty(value));
                    if let Some(t) = resolved {
                        if Self::type_has_list(&t) {
                            u.need_list = true;
                        }
                        self.local_env.insert(name.clone(), t);
                    }
                }
                Stmt::Assign {
                    target, op, value, ..
                } => {
                    if let AssignTarget::Index { index, .. } = target {
                        u.need_list = true;
                        self.scan_expr(index, u);
                    }
                    self.scan_expr(value, u);
                    if *op == AssignOp::AddAssign
                        && (self.target_ty(target) == Some(Type::Str)
                            || self.expr_ty(value) == Some(Type::Str))
                    {
                        u.need_str_concat = true;
                    }
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    self.scan_expr(cond, u);
                    let saved = self.local_env.clone();
                    self.scan_stmts(then_body, u);
                    self.local_env = saved.clone();
                    self.scan_stmts(else_body, u);
                    self.local_env = saved;
                }
                Stmt::Match { expr, arms, .. } => {
                    self.scan_expr(expr, u);
                    if self.expr_ty(expr) == Some(Type::Str)
                        || arms.iter().any(|a| matches!(&a.pat, MatchPat::Str(_)))
                    {
                        u.need_eql = true;
                    }
                    for arm in arms {
                        let saved = self.local_env.clone();
                        self.scan_stmts(&arm.body, u);
                        self.local_env = saved;
                    }
                }
                Stmt::While { cond, body, .. } => {
                    self.scan_expr(cond, u);
                    let saved = self.local_env.clone();
                    self.scan_stmts(body, u);
                    self.local_env = saved;
                }
                Stmt::ForEach {
                    var, iter, body, ..
                } => {
                    u.need_list = true;
                    self.scan_expr(iter, u);
                    let saved = self.local_env.clone();
                    if let Some(Type::List(el)) = self.expr_ty(iter) {
                        self.local_env.insert(var.clone(), *el);
                    }
                    self.scan_stmts(body, u);
                    self.local_env = saved;
                }
                Stmt::ForRange {
                    var,
                    start,
                    end,
                    body,
                    ..
                } => {
                    self.scan_expr(start, u);
                    self.scan_expr(end, u);
                    let saved = self.local_env.clone();
                    self.local_env.insert(var.clone(), Type::Int);
                    self.scan_stmts(body, u);
                    self.local_env = saved;
                }
                Stmt::Return { value: Some(v), .. } => self.scan_expr(v, u),
                Stmt::Assert { cond, .. } => self.scan_expr(cond, u),
                Stmt::AssertEq { left, right, .. } => {
                    let eq = Expr::Binary {
                        op: BinOp::Eq,
                        left: Box::new(left.clone()),
                        right: Box::new(right.clone()),
                    };
                    self.scan_expr(&eq, u);
                }
                Stmt::Expr { expr, .. } => self.scan_expr(expr, u),
                _ => {}
            }
        }
    }

    fn scan_expr(&mut self, expr: &Expr, u: &mut ZigUsage) {
        match expr {
            Expr::List(items) => {
                u.need_list = true;
                for it in items {
                    self.scan_expr(it, u);
                }
            }
            Expr::StructInit { fields, .. } => {
                for (_, v) in fields {
                    self.scan_expr(v, u);
                }
            }
            Expr::FieldAccess { base, .. } => self.scan_expr(base, u),
            Expr::Index { base, index } => {
                u.need_list = true;
                self.scan_expr(base, u);
                self.scan_expr(index, u);
            }
            Expr::Unary { expr: inner, .. } => self.scan_expr(inner, u),
            Expr::Binary { op, left, right } => {
                self.scan_expr(left, u);
                self.scan_expr(right, u);
                let lty = self.expr_ty(left).or_else(|| self.expr_ty(right));
                match op {
                    BinOp::Add if lty == Some(Type::Str) => {
                        u.need_str_concat = true;
                    }
                    BinOp::Eq | BinOp::Ne
                        if lty.as_ref().map(|t| self.type_needs_deep_eql(t)).unwrap_or(false) => {
                            u.need_eql = true;
                        }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge if lty == Some(Type::Str) => {
                        u.need_str_cmp = true;
                    }
                    _ => {}
                }
            }
            Expr::Call { args, .. } => {
                for a in args {
                    self.scan_expr(a, u);
                }
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(x) => {
                    self.scan_expr(x, u);
                    if self.expr_ty(x) == Some(Type::Str)
                        || !matches!(x, Expr::Var(_) | Expr::FieldAccess { .. })
                    {
                        u.need_len = true;
                    }
                }
                Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                    self.scan_expr(a, u);
                    self.scan_expr(b, u);
                }
                Intrinsic::Abs(a) => {
                    u.need_abs = true;
                    self.scan_expr(a, u);
                }
                Intrinsic::Push { list, value } => {
                    u.need_list = true;
                    self.scan_expr(list, u);
                    self.scan_expr(value, u);
                }
                Intrinsic::Print(args) => {
                    u.need_println = true;
                    for a in args {
                        self.scan_expr(a, u);
                    }
                }
                Intrinsic::Contains { haystack, needle } => {
                    self.scan_expr(haystack, u);
                    self.scan_expr(needle, u);
                    if self.expr_ty(haystack) == Some(Type::Str) {
                        u.need_str_contains = true;
                    } else {
                        u.need_list = true;
                        u.need_eql = true;
                    }
                }
                Intrinsic::Upper(x) => {
                    u.need_upper = true;
                    self.scan_expr(x, u);
                }
                Intrinsic::Lower(x) => {
                    u.need_lower = true;
                    self.scan_expr(x, u);
                }
                Intrinsic::ToStr(x) => {
                    u.need_to_str = true;
                    self.scan_expr(x, u);
                }
            },
            _ => {}
        }
    }

    fn emit_module(&mut self, hub: &HubModule, u: &ZigUsage, out: &mut String) {
        out.push_str("const std = @import(\"std\");\n");
        if u.need_printf {
            out.push_str("extern \"c\" fn printf(fmt: [*:0]const u8, ...) c_int;\n");
        }
        if u.need_snprintf {
            out.push_str("extern \"c\" fn snprintf(buf: [*]u8, size: usize, fmt: [*:0]const u8, ...) c_int;\n");
        }
        if u.need_malloc {
            out.push_str("extern \"c\" fn malloc(size: usize) ?*anyopaque;\n");
        }

        let mut rt = String::new();
        if u.need_list {
            rt.push_str(
                r#"fn StarList(comptime T: type) type {
    return struct {
        const Self = @This();
        ptr: [*]T = undefined,
        length: usize = 0,
        cap: usize = 0,
        pub fn empty() Self {
            return Self{ .ptr = undefined, .length = 0, .cap = 0 };
        }
        pub fn of(items: []const T) Self {
            if (items.len == 0) return Self.empty();
            const raw = malloc(items.len * @sizeOf(T)) orelse @panic("oom");
            const dst: [*]T = @ptrCast(@alignCast(raw));
            @memcpy(dst[0..items.len], items);
            return Self{ .ptr = dst, .length = items.len, .cap = items.len };
        }
        pub fn len(self: Self) i64 {
            return @intCast(self.length);
        }
        pub fn slice(self: Self) []const T {
            if (self.length == 0) return &[_]T{};
            return self.ptr[0..self.length];
        }
        pub fn get(self: Self, idx: i64) T {
            if (idx < 0 or @as(usize, @intCast(idx)) >= self.length) @panic("index out of bounds");
            return self.ptr[@intCast(idx)];
        }
        pub fn set(self: *Self, idx: i64, val: T) void {
            if (idx < 0 or @as(usize, @intCast(idx)) >= self.length) @panic("index out of bounds");
            self.ptr[@intCast(idx)] = val;
        }
        pub fn push(self: *Self, val: T) void {
            if (self.length >= self.cap) {
                const nc: usize = if (self.cap == 0) 4 else self.cap * 2;
                const raw = malloc(nc * @sizeOf(T)) orelse @panic("oom");
                const nd: [*]T = @ptrCast(@alignCast(raw));
                if (self.length > 0) @memcpy(nd[0..self.length], self.ptr[0..self.length]);
                self.ptr = nd;
                self.cap = nc;
            }
            self.ptr[self.length] = val;
            self.length += 1;
        }
        pub fn contains(self: Self, needle: T) bool {
            var i: usize = 0;
            while (i < self.length) : (i += 1) {
                if (starEql(self.ptr[i], needle)) return true;
            }
            return false;
        }
    };
}
"#,
            );
        }

        if u.need_eql {
            rt.push_str(
                r#"fn starEql(a: anytype, b: @TypeOf(a)) bool {
    const T = @TypeOf(a);
    if (T == []const u8) return std.mem.eql(u8, a, b);
    switch (@typeInfo(T)) {
        .@"struct" => |info| {
            if (@hasDecl(T, "slice") and @hasField(T, "length") and @hasField(T, "cap")) {
                if (a.length != b.length) return false;
                var i: usize = 0;
                while (i < a.length) : (i += 1) {
                    if (!starEql(a.ptr[i], b.ptr[i])) return false;
                }
                return true;
            }
            inline for (info.fields) |f| {
                if (!starEql(@field(a, f.name), @field(b, f.name))) return false;
            }
            return true;
        },
        else => return a == b,
    }
}
fn starNeq(a: anytype, b: @TypeOf(a)) bool {
    return !starEql(a, b);
}
"#,
            );
        }

        if u.need_str_concat {
            rt.push_str(
                r#"fn starStrConcat(a: []const u8, b: []const u8) []const u8 {
    const total = a.len + b.len;
    if (total == 0) return "";
    const raw = malloc(total) orelse @panic("oom");
    const dst: [*]u8 = @ptrCast(raw);
    if (a.len > 0) @memcpy(dst[0..a.len], a);
    if (b.len > 0) @memcpy(dst[a.len..total], b);
    return dst[0..total];
}
"#,
            );
        }
        if u.need_str_cmp {
            rt.push_str(
                "fn starStrLt(a: []const u8, b: []const u8) bool { return std.mem.order(u8, a, b) == .lt; }\nfn starStrLe(a: []const u8, b: []const u8) bool { return std.mem.order(u8, a, b) != .gt; }\nfn starStrGt(a: []const u8, b: []const u8) bool { return std.mem.order(u8, a, b) == .gt; }\nfn starStrGe(a: []const u8, b: []const u8) bool { return std.mem.order(u8, a, b) != .lt; }\n",
            );
        }
        if u.need_str_contains {
            rt.push_str(
                "fn starStrContains(h: []const u8, n: []const u8) bool { return std.mem.indexOf(u8, h, n) != null; }\n",
            );
        }
        if u.need_upper {
            rt.push_str(
                r#"fn starToUpper(s: []const u8) []const u8 {
    if (s.len == 0) return "";
    const raw = malloc(s.len) orelse @panic("oom");
    const dst: [*]u8 = @ptrCast(raw);
    for (s, 0..) |ch, i| dst[i] = std.ascii.toUpper(ch);
    return dst[0..s.len];
}
"#,
            );
        }
        if u.need_lower {
            rt.push_str(
                r#"fn starToLower(s: []const u8) []const u8 {
    if (s.len == 0) return "";
    const raw = malloc(s.len) orelse @panic("oom");
    const dst: [*]u8 = @ptrCast(raw);
    for (s, 0..) |ch, i| dst[i] = std.ascii.toLower(ch);
    return dst[0..s.len];
}
"#,
            );
        }
        if u.need_to_str {
            rt.push_str(
                r#"fn starToStr(val: anytype) []const u8 {
    const T = @TypeOf(val);
    if (T == i64 or T == comptime_int) {
        const raw = malloc(32) orelse @panic("oom");
        const buf: [*]u8 = @ptrCast(raw);
        const n = snprintf(buf, 32, "%lld", @as(c_longlong, val));
        return buf[0..@intCast(n)];
    } else if (T == f64 or T == comptime_float) {
        const raw = malloc(64) orelse @panic("oom");
        const buf: [*]u8 = @ptrCast(raw);
        const n = snprintf(buf, 64, "%.15g", @as(f64, val));
        return buf[0..@intCast(n)];
    } else if (T == bool) {
        return if (val) "true" else "false";
    } else {
        return val;
    }
}
"#,
            );
        }
        if u.need_len {
            rt.push_str(
                r#"fn starLen(x: anytype) i64 {
    const T = @TypeOf(x);
    if (T == []const u8) return @intCast(x.len);
    return x.len();
}
"#,
            );
        }
        if u.need_abs {
            rt.push_str("fn starAbs(v: anytype) if (@TypeOf(v) == comptime_int) i64 else if (@TypeOf(v) == comptime_float) f64 else @TypeOf(v) { return if (v < 0) -v else v; }\n");
        }
        if u.need_println {
            rt.push_str(
                r#"fn starPrintln(args: anytype) void {
    inline for (args, 0..) |arg, idx| {
        if (idx > 0) _ = printf(" ");
        const T = @TypeOf(arg);
        if (T == i64 or T == comptime_int) {
            _ = printf("%lld", @as(c_longlong, arg));
        } else if (T == f64 or T == comptime_float) {
            _ = printf("%.15g", @as(f64, arg));
        } else if (T == bool) {
            _ = printf("%s", if (arg) @as([*:0]const u8, "true") else @as([*:0]const u8, "false"));
        } else {
            const s: []const u8 = arg;
            _ = printf("%.*s", @as(c_int, @intCast(s.len)), s.ptr);
        }
    }
    _ = printf("\n");
}
"#,
            );
        }

        if !rt.is_empty() {
            out.push('\n');
            out.push_str(&rt);
        }

        for item in &hub.items {
            out.push('\n');
            match item {
                Item::Enum(e) => self.fmt_enum(e, out),
                Item::Struct(s) => self.fmt_struct(s, out),
                Item::Function(f) => self.fmt_fn(f, out),
                Item::Test(t) => self.fmt_test(t, out),
            }
        }
    }

    fn fmt_enum(&self, e: &EnumDecl, out: &mut String) {
        for c in &e.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("pub const {} = enum(i64) {{\n", e.name));
        for (idx, v) in e.variants.iter().enumerate() {
            out.push_str(&format!("    {} = {},\n", v, idx));
        }
        out.push_str("};\n");
    }

    fn fmt_struct(&self, s: &StructDecl, out: &mut String) {
        for c in &s.comments {
            out.push_str(&format!("// {}\n", c));
        }
        out.push_str(&format!("pub const {} = struct {{\n", s.name));
        for f in &s.fields {
            out.push_str(&format!("    {}: {},\n", f.name, Self::fmt_type(&f.ty)));
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
        let params_str = f
            .params
            .iter()
            .map(|p| format!("{}: {}", p.name, Self::fmt_type(&p.ty)))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(
            "pub fn {}({}) {} {{\n",
            f.name,
            params_str,
            Self::fmt_type(&f.ret_ty)
        ));
        for p in &f.params {
            if !stmts_ref_var(&f.body, &p.name) {
                out.push_str(&format!("    _ = {};\n", p.name));
            }
        }
        self.fmt_block_stmts(&f.body, 1, false, out);
        if f.ret_ty != Type::Void && !zig_block_terminates(&f.body) {
            out.push_str("    unreachable;\n");
        }
        out.push_str("}\n");
    }

    fn fmt_test(&mut self, t: &TestDecl, out: &mut String) {
        for c in &t.comments {
            out.push_str(&format!("// {}\n", c));
        }
        self.local_env.clear();
        out.push_str(&format!("test \"{}\" {{\n", escape_str(&t.name)));
        self.fmt_block_stmts(&t.body, 1, true, out);
        out.push_str("}\n");
    }

    fn fmt_block_stmts(
        &mut self,
        stmts: &[Stmt],
        indent: usize,
        in_test: bool,
        out: &mut String,
    ) {
        let pad = "    ".repeat(indent);
        for (idx, stmt) in stmts.iter().enumerate() {
            let rest = &stmts[idx + 1..];
            self.fmt_stmt(stmt, rest, indent, in_test, out);
            if let Stmt::Let {
                name, mutable, ..
            } = stmt
            {
                if *mutable {
                    if !stmts_mutate_var(rest, name) || !stmts_ref_var(rest, name) {
                        out.push_str(&format!("{}_ = &{};\n", pad, name));
                    }
                } else if !stmts_ref_var(rest, name) {
                    out.push_str(&format!("{}_ = {};\n", pad, name));
                }
            }
        }
    }

    fn fmt_stmt(
        &mut self,
        stmt: &Stmt,
        _rest: &[Stmt],
        indent: usize,
        in_test: bool,
        out: &mut String,
    ) {
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
                let kw = if *mutable { "var" } else { "const" };
                let resolved_ty = ty
                    .clone()
                    .or_else(|| self.expr_ty(value))
                    .unwrap_or(Type::Int);
                let val_str = match (&resolved_ty, value) {
                    (Type::List(inner), Expr::List(items)) if items.is_empty() => {
                        format!("StarList({}).empty()", Self::fmt_type(inner))
                    }
                    _ => self.fmt_expr(value),
                };
                out.push_str(&format!(
                    "{}{} {}: {} = {};\n",
                    pad,
                    kw,
                    name,
                    Self::fmt_type(&resolved_ty),
                    val_str
                ));
                self.local_env.insert(name.clone(), resolved_ty);
            }
            Stmt::Assign {
                target, op, value, ..
            } => {
                let is_str = self.target_ty(target) == Some(Type::Str)
                    || self.expr_ty(value) == Some(Type::Str);
                match target {
                    AssignTarget::Index { base, index } => {
                        let idx_s = self.fmt_expr(index);
                        let val_s = self.fmt_expr(value);
                        match op {
                            AssignOp::Set => {
                                out.push_str(&format!(
                                    "{}{}.set({}, {});\n",
                                    pad, base, idx_s, val_s
                                ));
                            }
                            AssignOp::AddAssign if is_str => {
                                out.push_str(&format!(
                                    "{}{}.set({}, starStrConcat({}.get({}), {}));\n",
                                    pad, base, idx_s, base, idx_s, val_s
                                ));
                            }
                            AssignOp::AddAssign => {
                                out.push_str(&format!(
                                    "{}{}.set({}, {}.get({}) + ({}));\n",
                                    pad, base, idx_s, base, idx_s, val_s
                                ));
                            }
                            AssignOp::SubAssign => {
                                out.push_str(&format!(
                                    "{}{}.set({}, {}.get({}) - ({}));\n",
                                    pad, base, idx_s, base, idx_s, val_s
                                ));
                            }
                        }
                    }
                    AssignTarget::Var(v) => {
                        if *op == AssignOp::AddAssign && is_str {
                            out.push_str(&format!(
                                "{}{} = starStrConcat({}, {});\n",
                                pad,
                                v,
                                v,
                                self.fmt_expr(value)
                            ));
                        } else {
                            let op_s = match op {
                                AssignOp::Set => "=",
                                AssignOp::AddAssign => "+=",
                                AssignOp::SubAssign => "-=",
                            };
                            out.push_str(&format!(
                                "{}{} {} {};\n",
                                pad,
                                v,
                                op_s,
                                self.fmt_expr(value)
                            ));
                        }
                    }
                    AssignTarget::Field { base, field } => {
                        if *op == AssignOp::AddAssign && is_str {
                            out.push_str(&format!(
                                "{}{}.{} = starStrConcat({}.{}, {});\n",
                                pad,
                                base,
                                field,
                                base,
                                field,
                                self.fmt_expr(value)
                            ));
                        } else {
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
                    }
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.fmt_if_chain(cond, then_body, else_body, indent, true, in_test, out);
            }
            Stmt::Match { expr, arms, .. } => {
                let scrut_ty = self.expr_ty(expr);
                if scrut_ty == Some(Type::Str)
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
                            let pat_s = match &arm.pat {
                                MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
                                MatchPat::Int(v) => v.to_string(),
                                MatchPat::EnumVariant { enum_name, variant } => {
                                    format!("{}.{}", enum_name, variant)
                                }
                                MatchPat::Wildcard => unreachable!(),
                            };
                            let cond_str = format!("starEql({}, {})", scrut, pat_s);
                            if idx == 0 {
                                out.push_str(&format!("{}if ({}) {{\n", pad, cond_str));
                            } else {
                                out.push_str(&format!(" else if ({}) {{\n", cond_str));
                            }
                        }
                        let saved = self.local_env.clone();
                        self.fmt_block_stmts(&arm.body, indent + 1, in_test, out);
                        self.local_env = saved;
                        out.push_str(&format!("{}}}", pad));
                    }
                    out.push('\n');
                } else {
                    out.push_str(&format!("{}switch ({}) {{\n", pad, self.fmt_expr(expr)));
                    let arm_pad = "    ".repeat(indent + 1);
                    let mut has_wildcard = false;
                    let mut covered_variants: HashSet<String> = HashSet::new();
                    for arm in arms {
                        let pat_str = match &arm.pat {
                            MatchPat::EnumVariant { enum_name, variant } => {
                                covered_variants.insert(variant.clone());
                                format!("{}.{}", enum_name, variant)
                            }
                            MatchPat::Int(v) => v.to_string(),
                            MatchPat::Str(s) => format!("\"{}\"", escape_str(s)),
                            MatchPat::Wildcard => {
                                has_wildcard = true;
                                "else".to_string()
                            }
                        };
                        out.push_str(&format!("{}{} => {{\n", arm_pad, pat_str));
                        let saved = self.local_env.clone();
                        self.fmt_block_stmts(&arm.body, indent + 2, in_test, out);
                        self.local_env = saved;
                        out.push_str(&format!("{}}},\n", arm_pad));
                    }
                    if !has_wildcard {
                        let enum_exhaustive = match &scrut_ty {
                            Some(Type::Named(en)) => self
                                .enum_variants
                                .get(en)
                                .map(|vs| vs.iter().all(|v| covered_variants.contains(v)))
                                .unwrap_or(false),
                            _ => false,
                        };
                        if !enum_exhaustive {
                            out.push_str(&format!("{}else => unreachable,\n", arm_pad));
                        }
                    }
                    out.push_str(&format!("{}}}\n", pad));
                }
            }
            Stmt::While { cond, body, .. } => {
                out.push_str(&format!("{}while ({}) {{\n", pad, self.fmt_expr(cond)));
                let saved = self.local_env.clone();
                self.fmt_block_stmts(body, indent + 1, in_test, out);
                self.local_env = saved;
                out.push_str(&format!("{}}}\n", pad));
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                let iter_s = self.fmt_postfix(iter);
                let used = stmts_ref_var(body, var);
                if used {
                    out.push_str(&format!("{}for ({}.slice()) |{}| {{\n", pad, iter_s, var));
                } else {
                    out.push_str(&format!("{}for ({}.slice()) |_| {{\n", pad, iter_s));
                    out.push_str(&format!("{}    // @star-unused-var {}\n", pad, var));
                }
                let saved = self.local_env.clone();
                if let Some(Type::List(el)) = self.expr_ty(iter) {
                    self.local_env.insert(var.clone(), *el);
                } else {
                    self.local_env.insert(var.clone(), Type::Int);
                }
                self.fmt_block_stmts(body, indent + 1, in_test, out);
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
                out.push_str(&format!("{}{{\n", pad));
                out.push_str(&format!(
                    "{}    var {}: i64 = {};\n",
                    pad,
                    var,
                    self.fmt_expr(start)
                ));
                out.push_str(&format!(
                    "{}    while ({} < {}) : ({} += 1) {{\n",
                    pad,
                    var,
                    self.fmt_expr(end),
                    var
                ));
                let saved = self.local_env.clone();
                self.local_env.insert(var.clone(), Type::Int);
                self.fmt_block_stmts(body, indent + 2, in_test, out);
                self.local_env = saved;
                out.push_str(&format!("{}    }}\n", pad));
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
                if in_test {
                    out.push_str(&format!("{}try std.testing.expect({});\n", pad, s));
                } else {
                    out.push_str(&format!("{}std.debug.assert({});\n", pad, s));
                }
            }
            Stmt::AssertEq { left, right, .. } => {
                let eq_expr = Expr::Binary {
                    op: BinOp::Eq,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                let s = self.fmt_expr(&eq_expr);
                if in_test {
                    out.push_str(&format!("{}try std.testing.expect({});\n", pad, s));
                } else {
                    out.push_str(&format!("{}std.debug.assert({});\n", pad, s));
                }
            }
            Stmt::Expr { expr, .. } => {
                let s = self.fmt_expr(expr);
                let is_void = self.expr_ty(expr) == Some(Type::Void)
                    || matches!(
                        expr,
                        Expr::Intrinsic(intr)
                            if matches!(intr.as_ref(), Intrinsic::Print(_) | Intrinsic::Push { .. })
                    );
                if is_void {
                    out.push_str(&format!("{}{};\n", pad, s));
                } else {
                    out.push_str(&format!("{}_ = {};\n", pad, s));
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn fmt_if_chain(
        &mut self,
        cond: &Expr,
        then_body: &[Stmt],
        else_body: &[Stmt],
        indent: usize,
        first: bool,
        in_test: bool,
        out: &mut String,
    ) {
        let pad = "    ".repeat(indent);
        if first {
            out.push_str(&format!("{}if ({}) {{\n", pad, self.fmt_expr(cond)));
        } else {
            out.push_str(&format!(" else if ({}) {{\n", self.fmt_expr(cond)));
        }
        let saved = self.local_env.clone();
        self.fmt_block_stmts(then_body, indent + 1, in_test, out);
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
                self.fmt_if_chain(c2, t2, e2, indent, false, in_test, out);
            }
        } else {
            out.push_str(&format!("{}}} else {{\n", pad));
            let saved2 = self.local_env.clone();
            self.fmt_block_stmts(else_body, indent + 1, in_test, out);
            self.local_env = saved2;
            out.push_str(&format!("{}}}\n", pad));
        }
    }

    fn fmt_postfix(&self, expr: &Expr) -> String {
        let s = self.fmt_expr(expr);
        match expr {
            Expr::Var(_)
            | Expr::Call { .. }
            | Expr::FieldAccess { .. }
            | Expr::Index { .. }
            | Expr::StructInit { .. } => s,
            _ => format!("({})", s),
        }
    }

    fn fmt_expr(&self, expr: &Expr) -> String {
        match expr {
            Expr::Int(v) => v.to_string(),
            Expr::Float(v) => format_float(*v),
            Expr::Bool(b) => b.to_string(),
            Expr::Str(s) => format!("\"{}\"", escape_str(s)),
            Expr::Var(v) => v.clone(),
            Expr::EnumVariant { enum_name, variant } => format!("{}.{}", enum_name, variant),
            Expr::List(items) => {
                let elem_ty = items
                    .first()
                    .and_then(|e| self.expr_ty(e))
                    .unwrap_or(Type::Int);
                let elem_z = Self::fmt_type(&elem_ty);
                if items.is_empty() {
                    format!("StarList({}).empty()", elem_z)
                } else {
                    let vals = items
                        .iter()
                        .map(|e| self.fmt_expr(e))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("StarList({}).of(&[_]{}{{ {} }})", elem_z, elem_z, vals)
                }
            }
            Expr::StructInit { name, fields } => {
                if fields.is_empty() {
                    format!("{}{{}}", name)
                } else {
                    let fs = fields
                        .iter()
                        .map(|(fname, fval)| format!(".{} = {}", fname, self.fmt_expr(fval)))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}{{ {} }}", name, fs)
                }
            }
            Expr::FieldAccess { base, field } => format!("{}.{}", self.fmt_postfix(base), field),
            Expr::Index { base, index } => {
                format!("{}.get({})", self.fmt_postfix(base), self.fmt_expr(index))
            }
            Expr::Unary { op, expr: inner } => {
                let inner_s = match inner.as_ref() {
                    Expr::Binary { .. } => format!("({})", self.fmt_expr(inner)),
                    Expr::Unary {
                        op: UnaryOp::Neg, ..
                    } if *op == UnaryOp::Neg => format!("({})", self.fmt_expr(inner)),
                    _ => self.fmt_expr(inner),
                };
                match op {
                    UnaryOp::Neg => format!("-{}", inner_s),
                    UnaryOp::Not => format!("!{}", inner_s),
                }
            }
            Expr::Binary { op, left, right } => {
                let lty = self.expr_ty(left).or_else(|| self.expr_ty(right));
                match op {
                    BinOp::Add if lty == Some(Type::Str) => {
                        return format!(
                            "starStrConcat({}, {})",
                            self.fmt_expr(left),
                            self.fmt_expr(right)
                        );
                    }
                    BinOp::Eq
                        if lty
                            .as_ref()
                            .map(|t| self.type_needs_deep_eql(t))
                            .unwrap_or(false) =>
                    {
                        return format!(
                            "starEql({}, {})",
                            self.fmt_expr(left),
                            self.fmt_expr(right)
                        );
                    }
                    BinOp::Ne
                        if lty
                            .as_ref()
                            .map(|t| self.type_needs_deep_eql(t))
                            .unwrap_or(false) =>
                    {
                        return format!(
                            "starNeq({}, {})",
                            self.fmt_expr(left),
                            self.fmt_expr(right)
                        );
                    }
                    BinOp::IntDiv => {
                        return format!(
                            "@divTrunc({}, {})",
                            self.fmt_expr(left),
                            self.fmt_expr(right)
                        );
                    }
                    BinOp::Mod => {
                        return format!(
                            "@rem({}, {})",
                            self.fmt_expr(left),
                            self.fmt_expr(right)
                        );
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge if lty == Some(Type::Str) => {
                        let fn_name = match op {
                            BinOp::Lt => "starStrLt",
                            BinOp::Le => "starStrLe",
                            BinOp::Gt => "starStrGt",
                            BinOp::Ge => "starStrGe",
                            _ => unreachable!(),
                        };
                        return format!(
                            "{}({}, {})",
                            fn_name,
                            self.fmt_expr(left),
                            self.fmt_expr(right)
                        );
                    }
                    _ => {}
                }

                let ls = if needs_parens(left, *op, false) {
                    format!("({})", self.fmt_expr(left))
                } else {
                    self.fmt_expr(left)
                };
                let rs = if needs_parens(right, *op, true) {
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
                    BinOp::And => "and",
                    BinOp::Or => "or",
                };
                format!("{} {} {}", ls, op_str, rs)
            }
            Expr::Call { func, args } => {
                let args_s = args
                    .iter()
                    .map(|a| self.fmt_expr(a))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", func, args_s)
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(x) => {
                    if self.expr_ty(x) == Some(Type::Str)
                        || !matches!(x, Expr::Var(_) | Expr::FieldAccess { .. })
                    {
                        format!("starLen({})", self.fmt_expr(x))
                    } else {
                        format!("{}.len()", self.fmt_postfix(x))
                    }
                }
                Intrinsic::Min(a, b) => format!("@min({}, {})", self.fmt_expr(a), self.fmt_expr(b)),
                Intrinsic::Max(a, b) => format!("@max({}, {})", self.fmt_expr(a), self.fmt_expr(b)),
                Intrinsic::Abs(a) => format!("starAbs({})", self.fmt_expr(a)),
                Intrinsic::Push { list, value } => {
                    format!("{}.push({})", self.fmt_postfix(list), self.fmt_expr(value))
                }
                Intrinsic::Print(args) => {
                    if args.is_empty() {
                        "starPrintln(.{})".to_string()
                    } else {
                        let joined = args
                            .iter()
                            .map(|a| self.fmt_expr(a))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("starPrintln(.{{ {} }})", joined)
                    }
                }
                Intrinsic::Contains { haystack, needle } => {
                    if self.expr_ty(haystack) == Some(Type::Str) {
                        format!(
                            "starStrContains({}, {})",
                            self.fmt_expr(haystack),
                            self.fmt_expr(needle)
                        )
                    } else {
                        format!(
                            "{}.contains({})",
                            self.fmt_postfix(haystack),
                            self.fmt_expr(needle)
                        )
                    }
                }
                Intrinsic::Upper(x) => format!("starToUpper({})", self.fmt_expr(x)),
                Intrinsic::Lower(x) => format!("starToLower({})", self.fmt_expr(x)),
                Intrinsic::ToStr(x) => format!("starToStr({})", self.fmt_expr(x)),
            },
        }
    }
}

fn stmts_ref_var(stmts: &[Stmt], target_var: &str) -> bool {
    for stmt in stmts {
        match stmt {
            Stmt::Comment { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {}
            Stmt::Let { name, value, .. } => {
                if expr_refs_var(value, target_var) {
                    return true;
                }
                if name == target_var {
                    return false;
                }
            }
            Stmt::Assign { target, value, .. } => {
                if target.root_var() == target_var || expr_refs_var(value, target_var) {
                    return true;
                }
                if let AssignTarget::Index { index, .. } = target {
                    if expr_refs_var(index, target_var) {
                        return true;
                    }
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                if expr_refs_var(cond, target_var)
                    || stmts_ref_var(then_body, target_var)
                    || stmts_ref_var(else_body, target_var)
                {
                    return true;
                }
            }
            Stmt::Match { expr, arms, .. } => {
                if expr_refs_var(expr, target_var)
                    || arms.iter().any(|a| stmts_ref_var(&a.body, target_var))
                {
                    return true;
                }
            }
            Stmt::While { cond, body, .. } => {
                if expr_refs_var(cond, target_var) || stmts_ref_var(body, target_var) {
                    return true;
                }
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                if expr_refs_var(iter, target_var) {
                    return true;
                }
                if var != target_var && stmts_ref_var(body, target_var) {
                    return true;
                }
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                if expr_refs_var(start, target_var) || expr_refs_var(end, target_var) {
                    return true;
                }
                if var != target_var && stmts_ref_var(body, target_var) {
                    return true;
                }
            }
            Stmt::Return { value: Some(v), .. } => {
                if expr_refs_var(v, target_var) {
                    return true;
                }
            }
            Stmt::Return { value: None, .. } => {}
            Stmt::Assert { cond, .. } => {
                if expr_refs_var(cond, target_var) {
                    return true;
                }
            }
            Stmt::AssertEq { left, right, .. } => {
                if expr_refs_var(left, target_var) || expr_refs_var(right, target_var) {
                    return true;
                }
            }
            Stmt::Expr { expr, .. } => {
                if expr_refs_var(expr, target_var) {
                    return true;
                }
            }
        }
    }
    false
}

fn expr_refs_var(expr: &Expr, target_var: &str) -> bool {
    match expr {
        Expr::Var(v) => v == target_var,
        Expr::List(items) => items.iter().any(|e| expr_refs_var(e, target_var)),
        Expr::StructInit { fields, .. } => fields.iter().any(|(_, e)| expr_refs_var(e, target_var)),
        Expr::FieldAccess { base, .. } => expr_refs_var(base, target_var),
        Expr::Index { base, index } => {
            expr_refs_var(base, target_var) || expr_refs_var(index, target_var)
        }
        Expr::Unary { expr: inner, .. } => expr_refs_var(inner, target_var),
        Expr::Binary { left, right, .. } => {
            expr_refs_var(left, target_var) || expr_refs_var(right, target_var)
        }
        Expr::Call { args, .. } => args.iter().any(|e| expr_refs_var(e, target_var)),
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(x)
            | Intrinsic::Abs(x)
            | Intrinsic::Upper(x)
            | Intrinsic::Lower(x)
            | Intrinsic::ToStr(x) => expr_refs_var(x, target_var),
            Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                expr_refs_var(a, target_var) || expr_refs_var(b, target_var)
            }
            Intrinsic::Push { list, value } => {
                expr_refs_var(list, target_var) || expr_refs_var(value, target_var)
            }
            Intrinsic::Print(args) => args.iter().any(|a| expr_refs_var(a, target_var)),
            Intrinsic::Contains { haystack, needle } => {
                expr_refs_var(haystack, target_var) || expr_refs_var(needle, target_var)
            }
        },
        _ => false,
    }
}

fn stmts_mutate_var(stmts: &[Stmt], target_var: &str) -> bool {
    for stmt in stmts {
        match stmt {
            Stmt::Assign { target, value, .. } => {
                if target.root_var() == target_var || expr_mutates_var(value, target_var) {
                    return true;
                }
            }
            Stmt::Let { name, value, .. } => {
                if expr_mutates_var(value, target_var) {
                    return true;
                }
                if name == target_var {
                    return false;
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                if expr_mutates_var(cond, target_var)
                    || stmts_mutate_var(then_body, target_var)
                    || stmts_mutate_var(else_body, target_var)
                {
                    return true;
                }
            }
            Stmt::Match { expr, arms, .. } => {
                if expr_mutates_var(expr, target_var)
                    || arms.iter().any(|a| stmts_mutate_var(&a.body, target_var))
                {
                    return true;
                }
            }
            Stmt::While { cond, body, .. } => {
                if expr_mutates_var(cond, target_var) || stmts_mutate_var(body, target_var) {
                    return true;
                }
            }
            Stmt::ForEach {
                var, iter, body, ..
            } => {
                if expr_mutates_var(iter, target_var) {
                    return true;
                }
                if var != target_var && stmts_mutate_var(body, target_var) {
                    return true;
                }
            }
            Stmt::ForRange {
                var,
                start,
                end,
                body,
                ..
            } => {
                if expr_mutates_var(start, target_var) || expr_mutates_var(end, target_var) {
                    return true;
                }
                if var != target_var && stmts_mutate_var(body, target_var) {
                    return true;
                }
            }
            Stmt::Return { value: Some(v), .. } => {
                if expr_mutates_var(v, target_var) {
                    return true;
                }
            }
            Stmt::Assert { cond, .. } => {
                if expr_mutates_var(cond, target_var) {
                    return true;
                }
            }
            Stmt::AssertEq { left, right, .. } => {
                if expr_mutates_var(left, target_var) || expr_mutates_var(right, target_var) {
                    return true;
                }
            }
            Stmt::Expr { expr, .. }
                if expr_mutates_var(expr, target_var) => {
                    return true;
                }
            _ => {}
        }
    }
    false
}

fn expr_mutates_var(expr: &Expr, target_var: &str) -> bool {
    match expr {
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Push { list, value } => {
                matches!(list, Expr::Var(v) if v == target_var)
                    || expr_mutates_var(list, target_var)
                    || expr_mutates_var(value, target_var)
            }
            Intrinsic::Len(x)
            | Intrinsic::Abs(x)
            | Intrinsic::Upper(x)
            | Intrinsic::Lower(x)
            | Intrinsic::ToStr(x) => expr_mutates_var(x, target_var),
            Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => {
                expr_mutates_var(a, target_var) || expr_mutates_var(b, target_var)
            }
            Intrinsic::Print(args) => args.iter().any(|a| expr_mutates_var(a, target_var)),
            Intrinsic::Contains { haystack, needle } => {
                expr_mutates_var(haystack, target_var) || expr_mutates_var(needle, target_var)
            }
        },
        Expr::Binary { left, right, .. } => {
            expr_mutates_var(left, target_var) || expr_mutates_var(right, target_var)
        }
        Expr::Unary { expr: inner, .. } | Expr::FieldAccess { base: inner, .. } => {
            expr_mutates_var(inner, target_var)
        }
        Expr::Index { base, index } => {
            expr_mutates_var(base, target_var) || expr_mutates_var(index, target_var)
        }
        Expr::Call { args, .. } | Expr::List(args) => {
            args.iter().any(|a| expr_mutates_var(a, target_var))
        }
        Expr::StructInit { fields, .. } => fields.iter().any(|(_, e)| expr_mutates_var(e, target_var)),
        _ => false,
    }
}

fn zig_block_terminates(stmts: &[Stmt]) -> bool {
    match stmts.last() {
        Some(Stmt::Return { .. }) => true,
        Some(Stmt::If {
            then_body,
            else_body,
            ..
        }) => !else_body.is_empty() && zig_block_terminates(then_body) && zig_block_terminates(else_body),
        Some(Stmt::Match { arms, .. }) => {
            !arms.is_empty() && arms.iter().all(|a| zig_block_terminates(&a.body))
        }
        _ => false,
    }
}

// ============================================================================
// Lexer & Recursive-Descent Parser (`put`) for Modern Zig 0.16
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
enum ZTokKind {
    Ident(String),
    Builtin(String), // `@import`, `@divTrunc`, `@rem`, `@min`, `@max`, `@as`, etc.
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
    Pipe,
    Amp,
    Question,
    Caret,
    Tilde,
    FatArrow, // `=>`
    Eq,
    EqEq,
    Bang,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusEq,
    MinusEq,
}

#[derive(Debug, Clone)]
struct ZToken {
    kind: ZTokKind,
    line: usize,
    col: usize,
}

fn lex_zig(src: &str) -> Result<Vec<ZToken>, Diagnostic> {
    let bytes = src.as_bytes();
    let n = bytes.len();
    let mut i = 0usize;
    let mut line = 1usize;
    let mut col = 1usize;
    let mut out = Vec::new();

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
            out.push(ZToken {
                kind: ZTokKind::Comment(text),
                line,
                col: start_col,
            });
            continue;
        }

        let tline = line;
        let tcol = col;

        // `@builtin` or `@"escaped"`
        if b == b'@' {
            i += 1;
            col += 1;
            if i < n && bytes[i] == b'"' {
                i += 1;
                col += 1;
                let s0 = i;
                while i < n && bytes[i] != b'"' {
                    i += 1;
                    col += 1;
                }
                if i >= n {
                    return Err(Diagnostic::new("zig", "unterminated @\"...\" identifier", tline, tcol));
                }
                let name = src[s0..i].to_string();
                i += 1;
                col += 1;
                out.push(ZToken {
                    kind: ZTokKind::Ident(name),
                    line: tline,
                    col: tcol,
                });
                continue;
            }
            let s0 = i;
            while i < n && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
                col += 1;
            }
            out.push(ZToken {
                kind: ZTokKind::Builtin(src[s0..i].to_string()),
                line: tline,
                col: tcol,
            });
            continue;
        }

        // String literal `"..."`
        if b == b'"' {
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
                    return Err(Diagnostic::new("zig", "unterminated string literal", tline, tcol));
                }
                i += 1;
                col += 1;
            }
            if i >= n {
                return Err(Diagnostic::new("zig", "unterminated string literal", tline, tcol));
            }
            let raw = &src[start..i];
            i += 1;
            col += 1;
            out.push(ZToken {
                kind: ZTokKind::Str(unescape_string(raw)),
                line: tline,
                col: tcol,
            });
            continue;
        }

        // Numbers
        if b.is_ascii_digit() {
            let start = i;
            let mut is_float = false;
            while i < n && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
                i += 1;
                col += 1;
            }
            if i + 1 < n && bytes[i] == b'.' && bytes[i + 1].is_ascii_digit() {
                is_float = true;
                i += 1;
                col += 1;
                while i < n && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
                    i += 1;
                    col += 1;
                }
            }
            let cleaned: String = src[start..i].chars().filter(|&c| c != '_').collect();
            if is_float {
                let v = cleaned
                    .parse::<f64>()
                    .map_err(|_| Diagnostic::new("zig", "invalid float literal", tline, tcol))?;
                out.push(ZToken {
                    kind: ZTokKind::Float(v),
                    line: tline,
                    col: tcol,
                });
            } else {
                let v = cleaned
                    .parse::<i64>()
                    .map_err(|_| Diagnostic::new("zig", "invalid integer literal", tline, tcol))?;
                out.push(ZToken {
                    kind: ZTokKind::Int(v),
                    line: tline,
                    col: tcol,
                });
            }
            continue;
        }

        // Identifiers / keywords
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            while i < n && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
                col += 1;
            }
            out.push(ZToken {
                kind: ZTokKind::Ident(src[start..i].to_string()),
                line: tline,
                col: tcol,
            });
            continue;
        }

        // Two-character tokens
        if i + 1 < n {
            let two = &src[i..i + 2];
            let kind2 = match two {
                "=>" => Some(ZTokKind::FatArrow),
                "==" => Some(ZTokKind::EqEq),
                "!=" => Some(ZTokKind::Ne),
                "<=" => Some(ZTokKind::Le),
                ">=" => Some(ZTokKind::Ge),
                "+=" => Some(ZTokKind::PlusEq),
                "-=" => Some(ZTokKind::MinusEq),
                _ => None,
            };
            if let Some(k) = kind2 {
                i += 2;
                col += 2;
                out.push(ZToken {
                    kind: k,
                    line: tline,
                    col: tcol,
                });
                continue;
            }
        }

        let kind1 = match b {
            b'(' => ZTokKind::LParen,
            b')' => ZTokKind::RParen,
            b'{' => ZTokKind::LBrace,
            b'}' => ZTokKind::RBrace,
            b'[' => ZTokKind::LBracket,
            b']' => ZTokKind::RBracket,
            b',' => ZTokKind::Comma,
            b';' => ZTokKind::Semi,
            b':' => ZTokKind::Colon,
            b'.' => ZTokKind::Dot,
            b'|' => ZTokKind::Pipe,
            b'&' => ZTokKind::Amp,
            b'?' => ZTokKind::Question,
            b'^' => ZTokKind::Caret,
            b'~' => ZTokKind::Tilde,
            b'=' => ZTokKind::Eq,
            b'!' => ZTokKind::Bang,
            b'<' => ZTokKind::Lt,
            b'>' => ZTokKind::Gt,
            b'+' => ZTokKind::Plus,
            b'-' => ZTokKind::Minus,
            b'*' => ZTokKind::Star,
            b'/' => ZTokKind::Slash,
            b'%' => ZTokKind::Percent,
            _ => {
                // Skip unknown characters Inside skipped helper bodies only if needed, otherwise error
                return Err(Diagnostic::new(
                    "zig",
                    format!("unexpected character '{}'", b as char),
                    tline,
                    tcol,
                ));
            }
        };
        i += 1;
        col += 1;
        out.push(ZToken {
            kind: kind1,
            line: tline,
            col: tcol,
        });
    }

    Ok(out)
}

fn prescan_zig_types(tokens: &[ZToken]) -> (HashSet<String>, HashSet<String>) {
    let mut structs = HashSet::new();
    let mut enums = HashSet::new();
    let mut i = 0;
    while i + 4 < tokens.len() {
        // `[pub] const <Name> = struct|enum`
        let mut p = i;
        if matches!(&tokens[p].kind, ZTokKind::Ident(s) if s == "pub") {
            p += 1;
        }
        if p + 3 < tokens.len()
            && matches!(&tokens[p].kind, ZTokKind::Ident(s) if s == "const")
            && matches!(&tokens[p + 2].kind, ZTokKind::Eq)
        {
            if let ZTokKind::Ident(name) = &tokens[p + 1].kind {
                if let ZTokKind::Ident(kw) = &tokens[p + 3].kind {
                    if kw == "struct" {
                        structs.insert(name.clone());
                    } else if kw == "enum" {
                        enums.insert(name.clone());
                    }
                }
            }
        }
        i += 1;
    }
    (structs, enums)
}

struct ZigParser<'a> {
    tokens: &'a [ZToken],
    pos: usize,
    known_structs: HashSet<String>,
    known_enums: HashSet<String>,
    variant_to_enum: HashMap<String, String>,
}

impl<'a> ZigParser<'a> {
    fn new(
        tokens: &'a [ZToken],
        known_structs: HashSet<String>,
        known_enums: HashSet<String>,
    ) -> Self {
        Self {
            tokens,
            pos: 0,
            known_structs,
            known_enums,
            variant_to_enum: HashMap::new(),
        }
    }

    fn peek(&self) -> Option<&'a ZToken> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&'a ZTokKind> {
        self.peek().map(|t| &t.kind)
    }

    fn cur_loc(&self) -> (usize, usize) {
        if let Some(t) = self.peek() {
            (t.line, t.col)
        } else if let Some(last) = self.tokens.last() {
            (last.line, last.col + 1)
        } else {
            (1, 1)
        }
    }

    fn err<T>(&self, msg: impl Into<String>) -> Result<T, Diagnostic> {
        let (l, c) = self.cur_loc();
        Err(Diagnostic::new("zig", msg, l, c))
    }

    fn next(&mut self) -> Option<&'a ZToken> {
        let t = self.tokens.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn eat(&mut self, kind: &ZTokKind) -> bool {
        if self.peek_kind() == Some(kind) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if matches!(self.peek_kind(), Some(ZTokKind::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: &ZTokKind, desc: &str) -> Result<(), Diagnostic> {
        if self.eat(kind) {
            Ok(())
        } else {
            self.err(format!("expected {}", desc))
        }
    }

    fn expect_ident(&mut self, desc: &str) -> Result<String, Diagnostic> {
        match self.peek_kind() {
            Some(ZTokKind::Ident(s)) => {
                let out = s.clone();
                self.pos += 1;
                Ok(out)
            }
            _ => self.err(format!("expected {}", desc)),
        }
    }

    fn skip_balanced_braces(&mut self) -> Result<(), Diagnostic> {
        self.expect(&ZTokKind::LBrace, "'{'")?;
        let mut depth = 1usize;
        while depth > 0 {
            match self.next().map(|t| &t.kind) {
                Some(ZTokKind::LBrace) => depth += 1,
                Some(ZTokKind::RBrace) => depth -= 1,
                Some(_) => {}
                None => return self.err("unclosed '{'"),
            }
        }
        Ok(())
    }

    fn skip_until_semi(&mut self) -> Result<(), Diagnostic> {
        while let Some(tok) = self.next() {
            if tok.kind == ZTokKind::Semi {
                return Ok(());
            }
        }
        self.err("expected ';'")
    }

    fn parse_module(&mut self) -> Result<HubModule, Diagnostic> {
        let mut items = Vec::new();
        let mut pending_comments: Vec<String> = Vec::new();

        while let Some(tok) = self.peek() {
            match &tok.kind {
                ZTokKind::Comment(c) => {
                    pending_comments.push(c.clone());
                    self.pos += 1;
                }
                ZTokKind::Ident(s) if s == "extern" => {
                    pending_comments.clear();
                    self.skip_until_semi()?;
                }
                // Private helper `fn StarList(...)` / `fn starEql(...)` (not `pub fn`)
                ZTokKind::Ident(s) if s == "fn" => {
                    pending_comments.clear();
                    // Check if this is a generated `star*` or `StarList` helper vs a user unexported fn
                    let fname = match self.tokens.get(self.pos + 1).map(|t| &t.kind) {
                        Some(ZTokKind::Ident(n)) => n.clone(),
                        _ => String::new(),
                    };
                    if fname == "StarList" || fname.starts_with("star") {
                        while let Some(k) = self.peek_kind() {
                            if *k == ZTokKind::LBrace {
                                break;
                            }
                            self.pos += 1;
                        }
                        self.skip_balanced_braces()?;
                    } else {
                        let comments = std::mem::take(&mut pending_comments);
                        items.push(Item::Function(self.parse_fn(comments)?));
                    }
                }
                // `const std = @import("std");`
                ZTokKind::Ident(s) if s == "const" => {
                    if matches!(self.tokens.get(self.pos + 1).map(|t| &t.kind), Some(ZTokKind::Ident(n)) if n == "std") {
                        pending_comments.clear();
                        self.skip_until_semi()?;
                    } else {
                        let comments = std::mem::take(&mut pending_comments);
                        items.push(self.parse_type_decl(comments)?);
                    }
                }
                ZTokKind::Ident(s) if s == "pub" => {
                    self.pos += 1;
                    let comments = std::mem::take(&mut pending_comments);
                    if self.peek_kind() == Some(&ZTokKind::Ident("const".to_string())) {
                        items.push(self.parse_type_decl(comments)?);
                    } else if self.peek_kind() == Some(&ZTokKind::Ident("fn".to_string())) {
                        items.push(Item::Function(self.parse_fn(comments)?));
                    } else {
                        return self.err("expected 'const' or 'fn' after 'pub'");
                    }
                }
                ZTokKind::Ident(s) if s == "test" => {
                    let comments = std::mem::take(&mut pending_comments);
                    items.push(Item::Test(self.parse_test(comments)?));
                }
                _ => return self.err("unexpected top-level token in Zig module"),
            }
        }

        Ok(HubModule { items, next_id: 1 })
    }

    fn parse_type_decl(&mut self, comments: Vec<String>) -> Result<Item, Diagnostic> {
        if !self.eat_kw("const") {
            return self.err("expected 'const' in type declaration");
        }
        let name = self.expect_ident("type name")?;
        self.expect(&ZTokKind::Eq, "'=' after type name")?;

        if self.eat_kw("enum") {
            if self.eat(&ZTokKind::LParen) {
                let _ = self.parse_type()?;
                self.expect(&ZTokKind::RParen, "')' after enum tag type")?;
            }
            self.expect(&ZTokKind::LBrace, "'{' after enum")?;
            let mut variants = Vec::new();
            while !matches!(self.peek_kind(), Some(ZTokKind::RBrace) | None) {
                if let Some(ZTokKind::Comment(_)) = self.peek_kind() {
                    self.pos += 1;
                    continue;
                }
                let v = self.expect_ident("enum variant")?;
                if self.eat(&ZTokKind::Eq) {
                    let _ = self.eat(&ZTokKind::Minus);
                    let _ = self.next();
                }
                self.variant_to_enum.insert(v.clone(), name.clone());
                variants.push(v);
                let _ = self.eat(&ZTokKind::Comma);
            }
            self.expect(&ZTokKind::RBrace, "'}' after enum")?;
            self.expect(&ZTokKind::Semi, "';' after enum")?;
            self.known_enums.insert(name.clone());
            Ok(Item::Enum(EnumDecl {
                id: 0,
                name,
                variants,
                comments,
                meta: Metadata::new(),
            }))
        } else if self.eat_kw("struct") {
            self.expect(&ZTokKind::LBrace, "'{' after struct")?;
            let mut fields = Vec::new();
            while !matches!(self.peek_kind(), Some(ZTokKind::RBrace) | None) {
                if let Some(ZTokKind::Comment(_)) = self.peek_kind() {
                    self.pos += 1;
                    continue;
                }
                let fname = self.expect_ident("struct field name")?;
                self.expect(&ZTokKind::Colon, "':' after struct field name")?;
                let fty = self.parse_type()?;
                let _ = self.eat(&ZTokKind::Comma);
                fields.push(Field {
                    id: 0,
                    name: fname,
                    ty: fty,
                    meta: Metadata::new(),
                });
            }
            self.expect(&ZTokKind::RBrace, "'}' after struct")?;
            self.expect(&ZTokKind::Semi, "';' after struct")?;
            self.known_structs.insert(name.clone());
            Ok(Item::Struct(StructDecl {
                id: 0,
                name,
                fields,
                comments,
                meta: Metadata::new(),
            }))
        } else {
            self.err("expected 'struct' or 'enum'")
        }
    }

    fn parse_type(&mut self) -> Result<Type, Diagnostic> {
        // Optional `!` error union prefix (e.g. `!void` on `main`)
        let _ = self.eat(&ZTokKind::Bang);
        // `[]const u8` (`Type::Str`) or `[]const T` / `[]T` (`Type::List(T)`)
        if self.eat(&ZTokKind::LBracket) {
            self.expect(&ZTokKind::RBracket, "']' in slice type")?;
            let _ = self.eat_kw("const");
            if self.eat_kw("u8") {
                return Ok(Type::Str);
            }
            let elem = self.parse_type()?;
            return Ok(Type::List(Box::new(elem)));
        }
        let ident = self.expect_ident("Zig type")?;
        if ident == "StarList" {
            self.expect(&ZTokKind::LParen, "'(' after StarList")?;
            let inner = self.parse_type()?;
            self.expect(&ZTokKind::RParen, "')' after StarList(T)")?;
            return Ok(Type::List(Box::new(inner)));
        }
        match ident.as_str() {
            "i64" | "i32" | "isize" | "usize" => Ok(Type::Int),
            "u8" => Ok(Type::Str),
            "f64" | "f32" => Ok(Type::Float),
            "bool" => Ok(Type::Bool),
            "void" => Ok(Type::Void),
            other => Ok(Type::Named(other.to_string())),
        }
    }

    fn parse_fn(&mut self, comments: Vec<String>) -> Result<FnDecl, Diagnostic> {
        if !self.eat_kw("fn") {
            return self.err("expected 'fn'");
        }
        let name = self.expect_ident("function name")?;
        self.expect(&ZTokKind::LParen, "'(' after function name")?;
        let mut params = Vec::new();
        while !matches!(self.peek_kind(), Some(ZTokKind::RParen) | None) {
            let pname = self.expect_ident("parameter name")?;
            self.expect(&ZTokKind::Colon, "':' after parameter name")?;
            let pty = self.parse_type()?;
            params.push(Param {
                id: 0,
                name: pname,
                ty: pty,
                meta: Metadata::new(),
            });
            if !self.eat(&ZTokKind::Comma) {
                break;
            }
        }
        self.expect(&ZTokKind::RParen, "')' after parameters")?;
        let ret_ty = self.parse_type()?;
        let body = self.parse_block()?;

        if name.starts_with("test_") && params.is_empty() && ret_ty == Type::Void {
            // Kept as Function only if not declared via `test "..."` — normalize handles tests
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

    fn parse_test(&mut self, comments: Vec<String>) -> Result<TestDecl, Diagnostic> {
        if !self.eat_kw("test") {
            return self.err("expected 'test'");
        }
        let raw_name = match self.peek_kind() {
            Some(ZTokKind::Str(s)) => {
                let v = s.clone();
                self.pos += 1;
                v
            }
            _ => self.expect_ident("test name string")?,
        };
        let name = raw_name
            .strip_prefix("test_")
            .unwrap_or(&raw_name)
            .to_string();
        let body = self.parse_block()?;
        Ok(TestDecl {
            id: 0,
            name,
            body,
            comments,
            meta: Metadata::new(),
        })
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        self.expect(&ZTokKind::LBrace, "'{'")?;
        let mut raw_stmts = Vec::new();
        while !matches!(self.peek_kind(), Some(ZTokKind::RBrace) | None) {
            if let Some(s) = self.parse_stmt_opt()? {
                raw_stmts.push(s);
            }
        }
        self.expect(&ZTokKind::RBrace, "'}'")?;

        // Coalesce top-level unbraced `var i: i64 = start; while (i < end) : (i += 1) { ... }`
        // into `Stmt::ForRange` when `i` is not referenced after the loop!
        Ok(coalesce_unbraced_for_ranges(raw_stmts))
    }

    fn parse_stmt_opt(&mut self) -> Result<Option<Stmt>, Diagnostic> {
        if let Some(ZTokKind::Comment(c)) = self.peek_kind().cloned() {
            self.pos += 1;
            if c.trim() == "@star-match" && self.eat_kw("if") {
                return Ok(Some(self.parse_star_string_match()?));
            }
            return Ok(Some(Stmt::Comment { id: 0, text: c }));
        }

        // Skip trailing `unreachable;`
        if self.eat_kw("unreachable") {
            self.expect(&ZTokKind::Semi, "';' after unreachable")?;
            return Ok(None);
        }

        // Scoped block `{ var k: i64 = start; while (k < end) : (k += 1) { ... } }` -> `ForRange`
        if self.peek_kind() == Some(&ZTokKind::LBrace) {
            return Ok(Some(self.parse_braced_for_range()?));
        }

        // Discard `_ = ...;`
        if matches!(self.peek_kind(), Some(ZTokKind::Ident(s)) if s == "_")
            && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&ZTokKind::Eq)
        {
            self.pos += 2;
            // `_ = &x;` or `_ = x;` variable/param discard -> skip!
            if self.eat(&ZTokKind::Amp) {
                let _ = self.expect_ident("discarded variable")?;
                self.expect(&ZTokKind::Semi, "';' after discard")?;
                return Ok(None);
            }
            if matches!(self.peek_kind(), Some(ZTokKind::Ident(_)))
                && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&ZTokKind::Semi)
            {
                self.pos += 2;
                return Ok(None);
            }
            let expr = self.parse_expr()?;
            self.expect(&ZTokKind::Semi, "';' after expression")?;
            return Ok(Some(Stmt::Expr {
                id: 0,
                expr,
                meta: Metadata::new(),
            }));
        }

        // `const x [: T] = expr;` or `var x [: T] = expr;`
        if self.peek_kind() == Some(&ZTokKind::Ident("const".to_string()))
            || self.peek_kind() == Some(&ZTokKind::Ident("var".to_string()))
        {
            let mutable = self.eat_kw("var");
            if !mutable {
                self.eat_kw("const");
            }
            let name = self.expect_ident("variable name")?;
            let ty = if self.eat(&ZTokKind::Colon) {
                Some(self.parse_type()?)
            } else {
                None
            };
            self.expect(&ZTokKind::Eq, "'=' in declaration")?;
            let val = self.parse_expr()?;
            self.expect(&ZTokKind::Semi, "';' after declaration")?;
            let mut meta = Metadata::new();
            if mutable {
                meta.insert("explicit_mut".to_string(), "true".to_string());
            }
            return Ok(Some(Stmt::Let {
                id: 0,
                name,
                mutable,
                ty,
                value: val,
                meta,
            }));
        }

        if self.eat_kw("if") {
            return Ok(Some(self.parse_if()?));
        }
        if self.eat_kw("switch") {
            return Ok(Some(self.parse_switch()?));
        }
        if self.eat_kw("while") {
            return Ok(Some(self.parse_while_or_range_tail()?));
        }
        if self.eat_kw("for") {
            return Ok(Some(self.parse_foreach()?));
        }
        if self.eat_kw("break") {
            self.expect(&ZTokKind::Semi, "';' after break")?;
            return Ok(Some(Stmt::Break { id: 0 }));
        }
        if self.eat_kw("continue") {
            self.expect(&ZTokKind::Semi, "';' after continue")?;
            return Ok(Some(Stmt::Continue { id: 0 }));
        }
        if self.eat_kw("return") {
            if self.eat(&ZTokKind::Semi) {
                return Ok(Some(Stmt::Return {
                    id: 0,
                    value: None,
                    meta: Metadata::new(),
                }));
            }
            let v = self.parse_expr()?;
            self.expect(&ZTokKind::Semi, "';' after return")?;
            return Ok(Some(Stmt::Return {
                id: 0,
                value: Some(v),
                meta: Metadata::new(),
            }));
        }

        // `try std.testing.expect(<cond>);`
        if self.eat_kw("try") {
            let call = self.parse_expr()?;
            self.expect(&ZTokKind::Semi, "';' after try")?;
            if let Expr::FieldAccess { .. } | Expr::Call { .. } | Expr::Intrinsic(_) = &call {
                if let Some(cond) = extract_zig_assert_cond(call) {
                    return Ok(Some(Stmt::Assert {
                        id: 0,
                        cond,
                        meta: Metadata::new(),
                    }));
                }
            }
            return self.err("unsupported 'try' statement");
        }

        let lhs = self.parse_expr()?;

        // Assignment `lhs = rhs;`, `lhs += rhs;`, `lhs -= rhs;`
        let assign_op = if self.eat(&ZTokKind::Eq) {
            Some(AssignOp::Set)
        } else if self.eat(&ZTokKind::PlusEq) {
            Some(AssignOp::AddAssign)
        } else if self.eat(&ZTokKind::MinusEq) {
            Some(AssignOp::SubAssign)
        } else {
            None
        };

        if let Some(op) = assign_op {
            let starts_with_str_concat =
                matches!(self.peek_kind(), Some(ZTokKind::Ident(s)) if s == "starStrConcat");
            let rhs = self.parse_expr()?;
            self.expect(&ZTokKind::Semi, "';' after assignment")?;
            let (final_op, final_rhs) = if op == AssignOp::Set && starts_with_str_concat {
                match rhs {
                    Expr::Binary {
                        op: BinOp::Add,
                        left,
                        right,
                    } if *left == lhs => (AssignOp::AddAssign, *right),
                    other => (op, other),
                }
            } else {
                (op, rhs)
            };
            let target = match lhs {
                Expr::Var(v) => AssignTarget::Var(v),
                Expr::FieldAccess { base, field } => match *base {
                    Expr::Var(b) => AssignTarget::Field { base: b, field },
                    _ => return self.err("field assignment base must be a variable"),
                },
                _ => return self.err("invalid assignment target"),
            };
            return Ok(Some(Stmt::Assign {
                id: 0,
                target,
                op: final_op,
                value: final_rhs,
                meta: Metadata::new(),
            }));
        }

        self.expect(&ZTokKind::Semi, "';' after expression")?;

        // Check `std.debug.assert(cond)` or `<base>.set(idx, val)`
        if let Some(cond) = extract_zig_assert_cond(lhs.clone()) {
            return Ok(Some(Stmt::Assert {
                id: 0,
                cond,
                meta: Metadata::new(),
            }));
        }
        if let Some(assign_stmt) = extract_starlist_set_stmt(&lhs) {
            return Ok(Some(assign_stmt));
        }

        Ok(Some(Stmt::Expr {
            id: 0,
            expr: lhs,
            meta: Metadata::new(),
        }))
    }

    fn parse_if(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&ZTokKind::LParen, "'(' after if")?;
        let cond = self.parse_expr()?;
        self.expect(&ZTokKind::RParen, "')'")?;
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
            self.expect(&ZTokKind::LParen, "'(' in @star-match")?;
            let cond = self.parse_expr()?;
            self.expect(&ZTokKind::RParen, "')' in @star-match")?;
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
        self.expect(&ZTokKind::LParen, "'(' after switch")?;
        let scrut = self.parse_expr()?;
        self.expect(&ZTokKind::RParen, "')'")?;
        self.expect(&ZTokKind::LBrace, "'{' after switch")?;
        let mut arms = Vec::new();
        while !matches!(self.peek_kind(), Some(ZTokKind::RBrace) | None) {
            if let Some(ZTokKind::Comment(_)) = self.peek_kind() {
                self.pos += 1;
                continue;
            }
            let pat = if self.eat_kw("else") {
                MatchPat::Wildcard
            } else if self.eat(&ZTokKind::Minus) {
                match self.next().map(|t| &t.kind) {
                    Some(ZTokKind::Int(v)) => MatchPat::Int(-v),
                    _ => return self.err("expected int after '-' in switch prong"),
                }
            } else if let Some(ZTokKind::Int(v)) = self.peek_kind().cloned() {
                self.pos += 1;
                MatchPat::Int(v)
            } else if self.eat(&ZTokKind::Dot) {
                // Shorthand `.Variant` resolved via declared enums
                let vr = self.expect_ident("enum variant")?;
                let enum_name = self.variant_to_enum.get(&vr).cloned().unwrap_or_default();
                MatchPat::EnumVariant {
                    enum_name,
                    variant: vr,
                }
            } else {
                let enum_name = self.expect_ident("enum name in switch")?;
                self.expect(&ZTokKind::Dot, "'.' in enum switch pattern")?;
                let variant = self.expect_ident("enum variant in switch")?;
                MatchPat::EnumVariant { enum_name, variant }
            };

            self.expect(&ZTokKind::FatArrow, "'=>' in switch")?;

            // Skip `else => unreachable,`
            if pat == MatchPat::Wildcard && self.eat_kw("unreachable") {
                let _ = self.eat(&ZTokKind::Comma);
                continue;
            }

            let body = if self.peek_kind() == Some(&ZTokKind::LBrace) {
                self.parse_block()?
            } else {
                let val = self.parse_expr()?;
                vec![Stmt::Return {
                    id: 0,
                    value: Some(val),
                    meta: Metadata::new(),
                }]
            };
            let _ = self.eat(&ZTokKind::Comma);
            arms.push(MatchArm { pat, body });
        }
        self.expect(&ZTokKind::RBrace, "'}' after switch")?;
        Ok(Stmt::Match {
            id: 0,
            expr: scrut,
            arms,
            meta: Metadata::new(),
        })
    }

    fn parse_while_or_range_tail(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&ZTokKind::LParen, "'(' after while")?;
        let cond = self.parse_expr()?;
        self.expect(&ZTokKind::RParen, "')'")?;
        if self.eat(&ZTokKind::Colon) {
            // Continue expression `: (i += 1)` — preserve as tagged `While` for range coalescing!
            self.expect(&ZTokKind::LParen, "'(' after ':' in while")?;
            let step_var = self.expect_ident("loop step variable")?;
            self.expect(&ZTokKind::PlusEq, "'+=' in while continue expression")?;
            let _ = self.parse_expr()?;
            self.expect(&ZTokKind::RParen, "')' after while continue expression")?;
            let body = self.parse_block()?;
            let mut meta = Metadata::new();
            meta.insert("zig._step_var".to_string(), step_var);
            return Ok(Stmt::While {
                id: 0,
                cond,
                body,
                meta,
            });
        }
        let body = self.parse_block()?;
        Ok(Stmt::While {
            id: 0,
            cond,
            body,
            meta: Metadata::new(),
        })
    }

    fn parse_braced_for_range(&mut self) -> Result<Stmt, Diagnostic> {
        let mut block = self.parse_block()?;
        if block.len() == 1 && matches!(&block[0], Stmt::ForRange { .. }) {
            return Ok(block.remove(0));
        }
        self.err("unexpected standalone braced block in Zig")
    }

    fn parse_foreach(&mut self) -> Result<Stmt, Diagnostic> {
        self.expect(&ZTokKind::LParen, "'(' after for")?;
        let mut iter = self.parse_expr()?;
        // Unwrap `<expr>.slice()`
        if let Expr::Call { func, args } = &iter {
            if args.is_empty() && func.ends_with(".slice") {
                // Handled in postfix below (`MethodSlice`), fallback safety
            }
        }
        if let Some(unwrapped) = unwrap_slice_marker(iter.clone()) {
            iter = unwrapped;
        }
        self.expect(&ZTokKind::RParen, "')' after for iterable")?;
        self.expect(&ZTokKind::Pipe, "'|' before for capture")?;
        let raw_cap = self.expect_ident("for capture variable")?;
        self.expect(&ZTokKind::Pipe, "'|' after for capture")?;
        let mut body = self.parse_block()?;
        let mut var = raw_cap;
        if var == "_" {
            if let Some(Stmt::Comment { text, .. }) = body.first() {
                if let Some(orig) = text.trim().strip_prefix("@star-unused-var ") {
                    var = orig.trim().to_string();
                    body.remove(0);
                }
            }
        }
        Ok(Stmt::ForEach {
            id: 0,
            var,
            iter,
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
        let mut left = self.parse_add()?;
        loop {
            let op = match self.peek_kind() {
                Some(ZTokKind::EqEq) => BinOp::Eq,
                Some(ZTokKind::Ne) => BinOp::Ne,
                Some(ZTokKind::Lt) => BinOp::Lt,
                Some(ZTokKind::Le) => BinOp::Le,
                Some(ZTokKind::Gt) => BinOp::Gt,
                Some(ZTokKind::Ge) => BinOp::Ge,
                _ => break,
            };
            self.pos += 1;
            let right = self.parse_add()?;
            left = Expr::Binary {
                op,
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
                Some(ZTokKind::Plus) => BinOp::Add,
                Some(ZTokKind::Minus) => BinOp::Sub,
                _ => break,
            };
            self.pos += 1;
            let right = self.parse_mul()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_mul(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.parse_unary()?;
        loop {
            let op = match self.peek_kind() {
                Some(ZTokKind::Star) => BinOp::Mul,
                Some(ZTokKind::Slash) => BinOp::Div,
                Some(ZTokKind::Percent) => BinOp::Mod,
                _ => break,
            };
            self.pos += 1;
            let right = self.parse_unary()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Expr, Diagnostic> {
        if self.eat(&ZTokKind::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(inner),
            });
        }
        if self.eat(&ZTokKind::Bang) {
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
            if self.eat(&ZTokKind::Dot) {
                let member = self.expect_ident("field or method name")?;
                // Enum variant `EnumName.Variant`
                if let Expr::Var(ref base_name) = expr {
                    if self.known_enums.contains(base_name) {
                        expr = Expr::EnumVariant {
                            enum_name: base_name.clone(),
                            variant: member,
                        };
                        continue;
                    }
                    // `std.testing.expect(...)` or `std.debug.assert(...)`
                    if base_name == "std"
                        && self.eat(&ZTokKind::Dot) {
                            let leaf = self.expect_ident("std member")?;
                            if self.eat(&ZTokKind::LParen) {
                                let args = self.parse_arg_list()?;
                                expr = Expr::Call {
                                    func: format!("std.{}.{}", member, leaf),
                                    args,
                                };
                                continue;
                            }
                        }
                }

                if self.eat(&ZTokKind::LParen) {
                    let args = self.parse_arg_list()?;
                    expr = match (member.as_str(), args.len()) {
                        ("len", 0) => Expr::intrinsic(Intrinsic::Len(expr)),
                        ("get", 1) => Expr::Index {
                            base: Box::new(expr),
                            index: Box::new(args.into_iter().next().unwrap()),
                        },
                        ("push", 1) => Expr::intrinsic(Intrinsic::Push {
                            list: expr,
                            value: args.into_iter().next().unwrap(),
                        }),
                        ("contains", 1) => Expr::intrinsic(Intrinsic::Contains {
                            haystack: expr,
                            needle: args.into_iter().next().unwrap(),
                        }),
                        ("slice", 0) => wrap_slice_marker(expr),
                        ("set", 2) => {
                            let mut it = args.into_iter();
                            let idx = it.next().unwrap();
                            let val = it.next().unwrap();
                            Expr::Call {
                                func: "__starlist_set".to_string(),
                                args: vec![expr, idx, val],
                            }
                        }
                        _ => {
                            return self.err(format!("unsupported Zig method '.{}()'", member));
                        }
                    };
                } else {
                    expr = Expr::FieldAccess {
                        base: Box::new(expr),
                        field: member,
                    };
                }
            } else if self.eat(&ZTokKind::LBracket) {
                let idx = self.parse_expr()?;
                self.expect(&ZTokKind::RBracket, "']'")?;
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
            Some(ZTokKind::Int(v)) => {
                self.pos += 1;
                Ok(Expr::Int(v))
            }
            Some(ZTokKind::Float(v)) => {
                self.pos += 1;
                Ok(Expr::Float(v))
            }
            Some(ZTokKind::Str(s)) => {
                self.pos += 1;
                Ok(Expr::Str(s))
            }
            Some(ZTokKind::LParen) => {
                self.pos += 1;
                let e = self.parse_expr()?;
                self.expect(&ZTokKind::RParen, "')'")?;
                Ok(e)
            }
            Some(ZTokKind::Builtin(b)) => {
                self.pos += 1;
                self.expect(&ZTokKind::LParen, "'(' after builtin")?;
                let args = self.parse_arg_list()?;
                match (b.as_str(), args.len()) {
                    ("divTrunc", 2) => {
                        let mut it = args.into_iter();
                        Ok(Expr::Binary {
                            op: BinOp::IntDiv,
                            left: Box::new(it.next().unwrap()),
                            right: Box::new(it.next().unwrap()),
                        })
                    }
                    ("rem", 2) => {
                        let mut it = args.into_iter();
                        Ok(Expr::Binary {
                            op: BinOp::Mod,
                            left: Box::new(it.next().unwrap()),
                            right: Box::new(it.next().unwrap()),
                        })
                    }
                    ("min", 2) => {
                        let mut it = args.into_iter();
                        Ok(Expr::intrinsic(Intrinsic::Min(
                            it.next().unwrap(),
                            it.next().unwrap(),
                        )))
                    }
                    ("max", 2) => {
                        let mut it = args.into_iter();
                        Ok(Expr::intrinsic(Intrinsic::Max(
                            it.next().unwrap(),
                            it.next().unwrap(),
                        )))
                    }
                    ("intCast", 1) => Ok(args.into_iter().next().unwrap()),
                    _ => self.err(format!("unsupported Zig builtin '@{}'", b)),
                }
            }
            Some(ZTokKind::Amp) => {
                // `&[_]T{ e1, e2, ... }` slice literal
                self.pos += 1;
                self.expect(&ZTokKind::LBracket, "'[' after '&'")?;
                let _ = self.expect_ident("'_' in &[_]T")?;
                self.expect(&ZTokKind::RBracket, "']'")?;
                let _ = self.parse_type()?;
                self.expect(&ZTokKind::LBrace, "'{' in slice literal")?;
                let mut items = Vec::new();
                while !matches!(self.peek_kind(), Some(ZTokKind::RBrace) | None) {
                    items.push(self.parse_expr()?);
                    if !self.eat(&ZTokKind::Comma) {
                        break;
                    }
                }
                self.expect(&ZTokKind::RBrace, "'}' after slice literal")?;
                Ok(Expr::List(items))
            }
            Some(ZTokKind::Ident(id)) => {
                self.pos += 1;
                if id == "true" {
                    return Ok(Expr::Bool(true));
                }
                if id == "false" {
                    return Ok(Expr::Bool(false));
                }

                // `StarList(T).empty()` or `StarList(T).of(&[_]T{ ... })`
                if id == "StarList" {
                    self.expect(&ZTokKind::LParen, "'(' after StarList")?;
                    let _ = self.parse_type()?;
                    self.expect(&ZTokKind::RParen, "')' after StarList(T)")?;
                    self.expect(&ZTokKind::Dot, "'.' after StarList(T)")?;
                    let ctor = self.expect_ident("'empty' or 'of' after StarList(T).")?;
                    self.expect(&ZTokKind::LParen, "'('")?;
                    if ctor == "empty" {
                        self.expect(&ZTokKind::RParen, "')'")?;
                        return Ok(Expr::List(Vec::new()));
                    } else if ctor == "of" || ctor == "fromSlice" {
                        let list_expr = self.parse_expr()?;
                        self.expect(&ZTokKind::RParen, "')'")?;
                        return Ok(list_expr);
                    } else {
                        return self.err(format!("unknown StarList constructor '{}'", ctor));
                    }
                }

                // `starPrintln(.{ a, b, ... })`
                if id == "starPrintln" && self.eat(&ZTokKind::LParen) {
                    self.expect(&ZTokKind::Dot, "'.' in starPrintln(.{ ... })")?;
                    self.expect(&ZTokKind::LBrace, "'{' in starPrintln(.{ ... })")?;
                    let mut args = Vec::new();
                    while !matches!(self.peek_kind(), Some(ZTokKind::RBrace) | None) {
                        args.push(self.parse_expr()?);
                        if !self.eat(&ZTokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&ZTokKind::RBrace, "'}' in starPrintln")?;
                    self.expect(&ZTokKind::RParen, "')' after starPrintln")?;
                    return Ok(Expr::intrinsic(Intrinsic::Print(args)));
                }

                // Struct literal `StructName{ .field = val, ... }`
                if self.known_structs.contains(&id) && self.eat(&ZTokKind::LBrace) {
                    let mut fields = Vec::new();
                    while !matches!(self.peek_kind(), Some(ZTokKind::RBrace) | None) {
                        self.expect(&ZTokKind::Dot, "'.' before struct field init")?;
                        let fname = self.expect_ident("struct field name")?;
                        self.expect(&ZTokKind::Eq, "'=' after struct field")?;
                        let fval = self.parse_expr()?;
                        fields.push((fname, fval));
                        if !self.eat(&ZTokKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&ZTokKind::RBrace, "'}' after struct literal")?;
                    return Ok(Expr::StructInit { name: id, fields });
                }

                // Function / helper call `foo(...)`
                if self.eat(&ZTokKind::LParen) {
                    let args = self.parse_arg_list()?;
                    return match (id.as_str(), args.len()) {
                        ("starEql", 2) => {
                            let mut it = args.into_iter();
                            Ok(Expr::Binary {
                                op: BinOp::Eq,
                                left: Box::new(it.next().unwrap()),
                                right: Box::new(it.next().unwrap()),
                            })
                        }
                        ("starEql", 3) => {
                            let mut it = args.into_iter();
                            let _ = it.next();
                            Ok(Expr::Binary {
                                op: BinOp::Eq,
                                left: Box::new(it.next().unwrap()),
                                right: Box::new(it.next().unwrap()),
                            })
                        }
                        ("starNeq", 2) => {
                            let mut it = args.into_iter();
                            Ok(Expr::Binary {
                                op: BinOp::Ne,
                                left: Box::new(it.next().unwrap()),
                                right: Box::new(it.next().unwrap()),
                            })
                        }
                        ("starStrLt", 2) => {
                            let mut it = args.into_iter();
                            Ok(Expr::Binary {
                                op: BinOp::Lt,
                                left: Box::new(it.next().unwrap()),
                                right: Box::new(it.next().unwrap()),
                            })
                        }
                        ("starStrLe", 2) => {
                            let mut it = args.into_iter();
                            Ok(Expr::Binary {
                                op: BinOp::Le,
                                left: Box::new(it.next().unwrap()),
                                right: Box::new(it.next().unwrap()),
                            })
                        }
                        ("starStrGt", 2) => {
                            let mut it = args.into_iter();
                            Ok(Expr::Binary {
                                op: BinOp::Gt,
                                left: Box::new(it.next().unwrap()),
                                right: Box::new(it.next().unwrap()),
                            })
                        }
                        ("starStrGe", 2) => {
                            let mut it = args.into_iter();
                            Ok(Expr::Binary {
                                op: BinOp::Ge,
                                left: Box::new(it.next().unwrap()),
                                right: Box::new(it.next().unwrap()),
                            })
                        }
                        ("starStrConcat", 2) => {
                            let mut it = args.into_iter();
                            Ok(Expr::Binary {
                                op: BinOp::Add,
                                left: Box::new(it.next().unwrap()),
                                right: Box::new(it.next().unwrap()),
                            })
                        }
                        ("starStrContains", 2) => {
                            let mut it = args.into_iter();
                            Ok(Expr::intrinsic(Intrinsic::Contains {
                                haystack: it.next().unwrap(),
                                needle: it.next().unwrap(),
                            }))
                        }
                        ("starToUpper", 1) => Ok(Expr::intrinsic(Intrinsic::Upper(
                            args.into_iter().next().unwrap(),
                        ))),
                        ("starToLower", 1) => Ok(Expr::intrinsic(Intrinsic::Lower(
                            args.into_iter().next().unwrap(),
                        ))),
                        ("starToStr", 1) => Ok(Expr::intrinsic(Intrinsic::ToStr(
                            args.into_iter().next().unwrap(),
                        ))),
                        ("starLen", 1) => Ok(Expr::intrinsic(Intrinsic::Len(
                            args.into_iter().next().unwrap(),
                        ))),
                        ("starAbs", 1) => Ok(Expr::intrinsic(Intrinsic::Abs(
                            args.into_iter().next().unwrap(),
                        ))),
                        _ => Ok(Expr::Call { func: id, args }),
                    };
                }

                Ok(Expr::Var(id))
            }
            _ => self.err("expected Zig expression"),
        }
    }

    fn parse_arg_list(&mut self) -> Result<Vec<Expr>, Diagnostic> {
        let mut args = Vec::new();
        while !matches!(self.peek_kind(), Some(ZTokKind::RParen) | None) {
            args.push(self.parse_expr()?);
            if !self.eat(&ZTokKind::Comma) {
                break;
            }
        }
        self.expect(&ZTokKind::RParen, "')'")?;
        Ok(args)
    }
}

fn wrap_slice_marker(expr: Expr) -> Expr {
    Expr::Call {
        func: "__starlist_slice".to_string(),
        args: vec![expr],
    }
}

fn unwrap_slice_marker(expr: Expr) -> Option<Expr> {
    if let Expr::Call { func, mut args } = expr {
        if func == "__starlist_slice" && args.len() == 1 {
            return Some(args.remove(0));
        }
    }
    None
}

fn extract_zig_assert_cond(expr: Expr) -> Option<Expr> {
    if let Expr::Call { func, mut args } = expr {
        if (func == "std.testing.expect" || func == "std.debug.assert") && args.len() == 1 {
            return Some(args.remove(0));
        }
    }
    None
}

fn extract_starlist_set_stmt(expr: &Expr) -> Option<Stmt> {
    if let Expr::Call { func, args } = expr {
        if func == "__starlist_set" && args.len() == 3 {
            if let Expr::Var(base_var) = &args[0] {
                let idx = &args[1];
                let val = &args[2];
                // Detect `<base>.set(idx, <base>.get(idx) + v)` / `- v`!
                if let Expr::Binary { op, left, right } = val {
                    if matches!(op, BinOp::Add | BinOp::Sub) {
                        if let Expr::Index {
                            base: gbase,
                            index: gidx,
                        } = left.as_ref()
                        {
                            if **gbase == Expr::Var(base_var.clone()) && gidx.as_ref() == idx {
                                return Some(Stmt::Assign {
                                    id: 0,
                                    target: AssignTarget::Index {
                                        base: base_var.clone(),
                                        index: idx.clone(),
                                    },
                                    op: if *op == BinOp::Add {
                                        AssignOp::AddAssign
                                    } else {
                                        AssignOp::SubAssign
                                    },
                                    value: (**right).clone(),
                                    meta: Metadata::new(),
                                });
                            }
                        }
                    }
                }
                return Some(Stmt::Assign {
                    id: 0,
                    target: AssignTarget::Index {
                        base: base_var.clone(),
                        index: idx.clone(),
                    },
                    op: AssignOp::Set,
                    value: val.clone(),
                    meta: Metadata::new(),
                });
            }
        }
    }
    None
}

fn coalesce_unbraced_for_ranges(stmts: Vec<Stmt>) -> Vec<Stmt> {
    let mut out = Vec::with_capacity(stmts.len());
    let mut i = 0usize;
    while i < stmts.len() {
        if i + 1 < stmts.len() {
            if let (
                Stmt::Let {
                    name,
                    mutable: true,
                    value: start,
                    ..
                },
                Stmt::While {
                    cond:
                        Expr::Binary {
                            op: BinOp::Lt,
                            left,
                            right: end,
                        },
                    body,
                    meta: wmeta,
                    ..
                },
            ) = (&stmts[i], &stmts[i + 1])
            {
                if **left == Expr::Var(name.clone())
                    && wmeta.get("zig._step_var").map(|s| s.as_str()) == Some(name.as_str())
                    && !stmts_ref_var(&stmts[i + 2..], name)
                {
                    out.push(Stmt::ForRange {
                        id: 0,
                        var: name.clone(),
                        start: start.clone(),
                        end: (**end).clone(),
                        body: body.clone(),
                        meta: Metadata::new(),
                    });
                    i += 2;
                    continue;
                }
            }
        }
        let mut s = stmts[i].clone();
        if let Stmt::While { meta, body, .. } = &mut s {
            if let Some(step_var) = meta.remove("zig._step_var") {
                body.push(Stmt::Assign {
                    id: 0,
                    target: AssignTarget::Var(step_var),
                    op: AssignOp::AddAssign,
                    value: Expr::Int(1),
                    meta: Metadata::new(),
                });
            }
        }
        out.push(s);
        i += 1;
    }
    out
}

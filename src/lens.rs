use crate::hub::{BinOp, Diagnostic, Expr, HubModule};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpokeId {
    Rust,
    Zig,
    C,
    Cpp,
    Swift,
    Java,
    Go,
    Python,
    Ruby,
    Lua,
    TypeScript,
    Star,
}

impl SpokeId {
    pub const ALL: [SpokeId; 12] = [
        SpokeId::Rust,
        SpokeId::Zig,
        SpokeId::C,
        SpokeId::Cpp,
        SpokeId::Swift,
        SpokeId::Java,
        SpokeId::Go,
        SpokeId::Python,
        SpokeId::Ruby,
        SpokeId::Lua,
        SpokeId::TypeScript,
        SpokeId::Star,
    ];

    pub fn as_str(&self) -> &'static str {
        match self {
            SpokeId::Rust => "rust",
            SpokeId::Zig => "zig",
            SpokeId::C => "c",
            SpokeId::Cpp => "cpp",
            SpokeId::Swift => "swift",
            SpokeId::Java => "java",
            SpokeId::Go => "go",
            SpokeId::Python => "python",
            SpokeId::Ruby => "ruby",
            SpokeId::Lua => "lua",
            SpokeId::TypeScript => "typescript",
            SpokeId::Star => "star",
        }
    }

    pub fn display_name(&self) -> &'static str {
        match self {
            SpokeId::Rust => "Rust",
            SpokeId::Zig => "Zig",
            SpokeId::C => "C11",
            SpokeId::Cpp => "C++",
            SpokeId::Swift => "Swift",
            SpokeId::Java => "Java",
            SpokeId::Go => "Go",
            SpokeId::Python => "Python",
            SpokeId::Ruby => "Ruby",
            SpokeId::Lua => "Lua",
            SpokeId::TypeScript => "TypeScript",
            SpokeId::Star => "Star S-Expr",
        }
    }

    pub fn extension(&self) -> &'static str {
        match self {
            SpokeId::Rust => "rs",
            SpokeId::Zig => "zig",
            SpokeId::C => "c",
            SpokeId::Cpp => "cpp",
            SpokeId::Swift => "swift",
            SpokeId::Java => "java",
            SpokeId::Go => "go",
            SpokeId::Python => "py",
            SpokeId::Ruby => "rb",
            SpokeId::Lua => "lua",
            SpokeId::TypeScript => "ts",
            SpokeId::Star => "star",
        }
    }

    /// Metadata prefix owned by this spoke when reconciling edits.
    /// `None` means the spoke explicitly renders/parses all metadata keys (Star IR).
    pub fn meta_prefix(&self) -> Option<&'static str> {
        match self {
            SpokeId::Rust => Some("rust."),
            SpokeId::Zig => Some("zig."),
            SpokeId::C => Some("c."),
            SpokeId::Cpp => Some("cpp."),
            SpokeId::Swift => Some("swift."),
            SpokeId::Java => Some("java."),
            SpokeId::Go => Some("go."),
            SpokeId::Python => Some("py."),
            SpokeId::Ruby => Some("ruby."),
            SpokeId::Lua => Some("lua."),
            SpokeId::TypeScript => Some("ts."),
            SpokeId::Star => None,
        }
    }

    pub fn from_name_or_ext(s: &str) -> Option<Self> {
        match s.trim().to_ascii_lowercase().as_str() {
            "rust" | "rs" | ".rs" => Some(SpokeId::Rust),
            "zig" | ".zig" => Some(SpokeId::Zig),
            "c" | "c11" | ".c" => Some(SpokeId::C),
            "cpp" | "c++" | "cxx" | "cc" | ".cpp" | ".cc" | ".cxx" => Some(SpokeId::Cpp),
            "swift" | ".swift" => Some(SpokeId::Swift),
            "java" | ".java" => Some(SpokeId::Java),
            "go" | "golang" | ".go" => Some(SpokeId::Go),
            "python" | "py" | ".py" => Some(SpokeId::Python),
            "ruby" | "rb" | ".rb" => Some(SpokeId::Ruby),
            "lua" | "luajit" | ".lua" => Some(SpokeId::Lua),
            "typescript" | "ts" | ".ts" => Some(SpokeId::TypeScript),
            "star" | "sexpr" | "lisp" | ".star" => Some(SpokeId::Star),
            _ => None,
        }
    }
}

/// A bidirectional transformation (Symmetric/Putback Lens) connecting a concrete
/// language syntax to the central `HubModule`.
pub trait LanguageLens: Send + Sync {
    fn id(&self) -> SpokeId;

    /// Project (`get`): render the central Hub AST into idiomatic source code.
    fn get(&self, hub: &HubModule) -> String;

    /// Lift (`put`): parse edited source code and reconcile it with `prev_hub`
    /// so stable NodeIds and untouched metadata from other spokes survive.
    fn put(&self, source: &str, prev_hub: &HubModule) -> Result<HubModule, Diagnostic>;
}

pub fn binop_prec(op: BinOp) -> u8 {
    match op {
        BinOp::Or => 1,
        BinOp::And => 2,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 3,
        BinOp::Add | BinOp::Sub => 4,
        BinOp::Mul | BinOp::Div | BinOp::IntDiv | BinOp::Mod => 5,
    }
}

pub fn is_non_associative_right(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Sub
            | BinOp::Div
            | BinOp::IntDiv
            | BinOp::Mod
            | BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
    )
}

pub fn needs_parens(child: &Expr, parent_op: BinOp, is_right: bool) -> bool {
    match child {
        Expr::Binary { op: child_op, .. } => {
            let cp = binop_prec(*child_op);
            let pp = binop_prec(parent_op);
            let non_assoc_cmp = cp == 3 && pp == 3;
            cp < pp || (is_right && cp == pp) || non_assoc_cmp
        }
        _ => false,
    }
}

pub fn format_float(v: f64) -> String {
    let s = format!("{}", v);
    if s.contains('.') || s.contains('e') || s.contains('E') {
        s
    } else {
        format!("{}.0", s)
    }
}

pub fn escape_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            other => out.push(other),
        }
    }
    out
}

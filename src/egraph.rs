use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use crate::complexity::analyze_complexity;
use crate::eval::{eval_module_default, eval_tests_default};
use crate::hub::{
    AssignOp, AssignTarget, BinOp, Expr, FnDecl, HubModule, Intrinsic, Item, MatchPat, Stmt,
    UnaryOp,
};
use crate::lens::SpokeId;
use crate::spokes::lens_for;

pub type EClassId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EUnaryOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EBinOp {
    Add,
    Sub,
    Mul,
    Div,
    IntDiv,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ENode {
    Int(i64),
    FloatBits(u64),
    Bool(bool),
    Str(String),
    Var(String),
    EnumVariant {
        enum_name: String,
        variant: String,
    },
    List(Vec<EClassId>),
    StructInit {
        name: String,
        fields: Vec<(String, EClassId)>,
    },
    FieldAccess {
        base: EClassId,
        field: String,
    },
    Index {
        base: EClassId,
        index: EClassId,
    },
    Unary {
        op: EUnaryOp,
        arg: EClassId,
    },
    Binary {
        op: EBinOp,
        left: EClassId,
        right: EClassId,
    },
    Call {
        func: String,
        args: Vec<EClassId>,
    },
    Len(EClassId),
    Min(EClassId, EClassId),
    Max(EClassId, EClassId),
    Abs(EClassId),
    Push {
        list: EClassId,
        value: EClassId,
    },
    Print(Vec<EClassId>),
    Contains {
        haystack: EClassId,
        needle: EClassId,
    },
    Upper(EClassId),
    Lower(EClassId),
    ToStr(EClassId),
}

impl ENode {
    pub fn canonicalize(&self, uf_find: impl Fn(EClassId) -> EClassId) -> Self {
        match self {
            ENode::Int(_)
            | ENode::FloatBits(_)
            | ENode::Bool(_)
            | ENode::Str(_)
            | ENode::Var(_)
            | ENode::EnumVariant { .. } => self.clone(),
            ENode::List(items) => ENode::List(items.iter().map(|&c| uf_find(c)).collect()),
            ENode::StructInit { name, fields } => ENode::StructInit {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(k, c)| (k.clone(), uf_find(*c)))
                    .collect(),
            },
            ENode::FieldAccess { base, field } => ENode::FieldAccess {
                base: uf_find(*base),
                field: field.clone(),
            },
            ENode::Index { base, index } => ENode::Index {
                base: uf_find(*base),
                index: uf_find(*index),
            },
            ENode::Unary { op, arg } => ENode::Unary {
                op: *op,
                arg: uf_find(*arg),
            },
            ENode::Binary { op, left, right } => ENode::Binary {
                op: *op,
                left: uf_find(*left),
                right: uf_find(*right),
            },
            ENode::Call { func, args } => ENode::Call {
                func: func.clone(),
                args: args.iter().map(|&c| uf_find(c)).collect(),
            },
            ENode::Len(a) => ENode::Len(uf_find(*a)),
            ENode::Min(a, b) => ENode::Min(uf_find(*a), uf_find(*b)),
            ENode::Max(a, b) => ENode::Max(uf_find(*a), uf_find(*b)),
            ENode::Abs(a) => ENode::Abs(uf_find(*a)),
            ENode::Push { list, value } => ENode::Push {
                list: uf_find(*list),
                value: uf_find(*value),
            },
            ENode::Print(args) => ENode::Print(args.iter().map(|&c| uf_find(c)).collect()),
            ENode::Contains { haystack, needle } => ENode::Contains {
                haystack: uf_find(*haystack),
                needle: uf_find(*needle),
            },
            ENode::Upper(a) => ENode::Upper(uf_find(*a)),
            ENode::Lower(a) => ENode::Lower(uf_find(*a)),
            ENode::ToStr(a) => ENode::ToStr(uf_find(*a)),
        }
    }

    pub fn children(&self) -> Vec<EClassId> {
        match self {
            ENode::Int(_)
            | ENode::FloatBits(_)
            | ENode::Bool(_)
            | ENode::Str(_)
            | ENode::Var(_)
            | ENode::EnumVariant { .. } => Vec::new(),
            ENode::List(items) | ENode::Print(items) | ENode::Call { args: items, .. } => {
                items.clone()
            }
            ENode::StructInit { fields, .. } => fields.iter().map(|(_, c)| *c).collect(),
            ENode::FieldAccess { base, .. }
            | ENode::Unary { arg: base, .. }
            | ENode::Len(base)
            | ENode::Abs(base)
            | ENode::Upper(base)
            | ENode::Lower(base)
            | ENode::ToStr(base) => vec![*base],
            ENode::Index { base, index } => vec![*base, *index],
            ENode::Binary { left, right, .. }
            | ENode::Min(left, right)
            | ENode::Max(left, right)
            | ENode::Push {
                list: left,
                value: right,
            }
            | ENode::Contains {
                haystack: left,
                needle: right,
            } => vec![*left, *right],
        }
    }

    pub fn base_cost(&self) -> u64 {
        match self {
            ENode::Int(_)
            | ENode::FloatBits(_)
            | ENode::Bool(_)
            | ENode::Str(_)
            | ENode::Var(_)
            | ENode::EnumVariant { .. } => 1,
            ENode::Unary { .. } => 1,
            ENode::Binary { op, .. } => match op {
                EBinOp::Add
                | EBinOp::Sub
                | EBinOp::Eq
                | EBinOp::Ne
                | EBinOp::Lt
                | EBinOp::Le
                | EBinOp::Gt
                | EBinOp::Ge
                | EBinOp::And
                | EBinOp::Or => 2,
                EBinOp::Mul => 4,
                EBinOp::Div | EBinOp::IntDiv | EBinOp::Mod => 8,
            },
            ENode::Min(_, _)
            | ENode::Max(_, _)
            | ENode::Abs(_)
            | ENode::Len(_)
            | ENode::Upper(_)
            | ENode::Lower(_)
            | ENode::ToStr(_) => 3,
            ENode::FieldAccess { .. } | ENode::Index { .. } => 3,
            ENode::Call { .. }
            | ENode::List(_)
            | ENode::StructInit { .. }
            | ENode::Push { .. }
            | ENode::Print(_)
            | ENode::Contains { .. } => 5,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConstDatum {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
}

#[derive(Debug, Clone)]
pub struct EClass {
    pub id: EClassId,
    pub nodes: BTreeSet<ENode>,
    pub parents: Vec<(ENode, EClassId)>,
    pub const_val: Option<ConstDatum>,
}

pub struct EGraph {
    uf_parent: Vec<EClassId>,
    pub classes: BTreeMap<EClassId, EClass>,
    memo: BTreeMap<ENode, EClassId>,
    worklist: Vec<EClassId>,
    pub rules_fired: BTreeMap<String, usize>,
    pub total_unions: usize,
    pub iterations: usize,
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl EGraph {
    pub fn new() -> Self {
        Self {
            uf_parent: Vec::new(),
            classes: BTreeMap::new(),
            memo: BTreeMap::new(),
            worklist: Vec::new(),
            rules_fired: BTreeMap::new(),
            total_unions: 0,
            iterations: 0,
        }
    }

    pub fn find(&self, mut id: EClassId) -> EClassId {
        while self.uf_parent[id] != id {
            id = self.uf_parent[id];
        }
        id
    }

    pub fn total_enodes(&self) -> usize {
        self.classes.values().map(|c| c.nodes.len()).sum()
    }

    pub fn total_eclasses(&self) -> usize {
        self.classes.len()
    }

    pub fn add(&mut self, node: ENode) -> EClassId {
        let canon = node.canonicalize(|c| self.find(c));
        if let Some(&existing) = self.memo.get(&canon) {
            return self.find(existing);
        }

        let id = self.uf_parent.len();
        self.uf_parent.push(id);

        let const_val = match &canon {
            ENode::Int(v) => Some(ConstDatum::Int(*v)),
            ENode::FloatBits(bits) => Some(ConstDatum::Float(f64::from_bits(*bits))),
            ENode::Bool(b) => Some(ConstDatum::Bool(*b)),
            ENode::Str(s) => Some(ConstDatum::Str(s.clone())),
            _ => None,
        };

        for child in canon.children() {
            let cid = self.find(child);
            if let Some(cclass) = self.classes.get_mut(&cid) {
                cclass.parents.push((canon.clone(), id));
            }
        }

        let mut nodes = BTreeSet::new();
        nodes.insert(canon.clone());
        self.classes.insert(
            id,
            EClass {
                id,
                nodes,
                parents: Vec::new(),
                const_val,
            },
        );
        self.memo.insert(canon, id);
        id
    }

    pub fn add_expr(&mut self, expr: &Expr) -> EClassId {
        match expr {
            Expr::Int(v) => self.add(ENode::Int(*v)),
            Expr::Float(f) => {
                let norm = if *f == 0.0 { 0.0 } else { *f };
                self.add(ENode::FloatBits(norm.to_bits()))
            }
            Expr::Bool(b) => self.add(ENode::Bool(*b)),
            Expr::Str(s) => self.add(ENode::Str(s.clone())),
            Expr::Var(v) => self.add(ENode::Var(v.clone())),
            Expr::EnumVariant { enum_name, variant } => self.add(ENode::EnumVariant {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
            }),
            Expr::List(items) => {
                let ids = items.iter().map(|e| self.add_expr(e)).collect();
                self.add(ENode::List(ids))
            }
            Expr::StructInit { name, fields } => {
                let fids = fields
                    .iter()
                    .map(|(k, v)| (k.clone(), self.add_expr(v)))
                    .collect();
                self.add(ENode::StructInit {
                    name: name.clone(),
                    fields: fids,
                })
            }
            Expr::FieldAccess { base, field } => {
                let bid = self.add_expr(base);
                self.add(ENode::FieldAccess {
                    base: bid,
                    field: field.clone(),
                })
            }
            Expr::Index { base, index } => {
                let bid = self.add_expr(base);
                let iid = self.add_expr(index);
                self.add(ENode::Index {
                    base: bid,
                    index: iid,
                })
            }
            Expr::Unary { op, expr: inner } => {
                let aid = self.add_expr(inner);
                let eop = match op {
                    UnaryOp::Neg => EUnaryOp::Neg,
                    UnaryOp::Not => EUnaryOp::Not,
                };
                self.add(ENode::Unary { op: eop, arg: aid })
            }
            Expr::Binary { op, left, right } => {
                let lid = self.add_expr(left);
                let rid = self.add_expr(right);
                let eop = match op {
                    BinOp::Add => EBinOp::Add,
                    BinOp::Sub => EBinOp::Sub,
                    BinOp::Mul => EBinOp::Mul,
                    BinOp::Div => EBinOp::Div,
                    BinOp::IntDiv => EBinOp::IntDiv,
                    BinOp::Mod => EBinOp::Mod,
                    BinOp::Eq => EBinOp::Eq,
                    BinOp::Ne => EBinOp::Ne,
                    BinOp::Lt => EBinOp::Lt,
                    BinOp::Le => EBinOp::Le,
                    BinOp::Gt => EBinOp::Gt,
                    BinOp::Ge => EBinOp::Ge,
                    BinOp::And => EBinOp::And,
                    BinOp::Or => EBinOp::Or,
                };
                self.add(ENode::Binary {
                    op: eop,
                    left: lid,
                    right: rid,
                })
            }
            Expr::Call { func, args } => {
                let aids = args.iter().map(|a| self.add_expr(a)).collect();
                self.add(ENode::Call {
                    func: func.clone(),
                    args: aids,
                })
            }
            Expr::Intrinsic(intr) => match intr.as_ref() {
                Intrinsic::Len(a) => {
                    let id = self.add_expr(a);
                    self.add(ENode::Len(id))
                }
                Intrinsic::Min(a, b) => {
                    let ia = self.add_expr(a);
                    let ib = self.add_expr(b);
                    self.add(ENode::Min(ia, ib))
                }
                Intrinsic::Max(a, b) => {
                    let ia = self.add_expr(a);
                    let ib = self.add_expr(b);
                    self.add(ENode::Max(ia, ib))
                }
                Intrinsic::Abs(a) => {
                    let id = self.add_expr(a);
                    self.add(ENode::Abs(id))
                }
                Intrinsic::Push { list, value } => {
                    let il = self.add_expr(list);
                    let iv = self.add_expr(value);
                    self.add(ENode::Push {
                        list: il,
                        value: iv,
                    })
                }
                Intrinsic::Print(args) => {
                    let ids = args.iter().map(|a| self.add_expr(a)).collect();
                    self.add(ENode::Print(ids))
                }
                Intrinsic::Contains { haystack, needle } => {
                    let ih = self.add_expr(haystack);
                    let in_id = self.add_expr(needle);
                    self.add(ENode::Contains {
                        haystack: ih,
                        needle: in_id,
                    })
                }
                Intrinsic::Upper(a) => {
                    let id = self.add_expr(a);
                    self.add(ENode::Upper(id))
                }
                Intrinsic::Lower(a) => {
                    let id = self.add_expr(a);
                    self.add(ENode::Lower(id))
                }
                Intrinsic::ToStr(a) => {
                    let id = self.add_expr(a);
                    self.add(ENode::ToStr(id))
                }
            },
        }
    }

    pub fn union(&mut self, id1: EClassId, id2: EClassId) -> bool {
        let r1 = self.find(id1);
        let r2 = self.find(id2);
        if r1 == r2 {
            return false;
        }
        let (keep,drop_id) = if r1 < r2 { (r1, r2) } else { (r2, r1) };
        self.uf_parent[drop_id] = keep;
        self.total_unions += 1;

        if let Some(dropped) = self.classes.remove(&drop_id) {
            if let Some(target) = self.classes.get_mut(&keep) {
                for n in dropped.nodes {
                    target.nodes.insert(n);
                }
                target.parents.extend(dropped.parents);
                if target.const_val.is_none() {
                    target.const_val = dropped.const_val;
                }
            }
        }
        self.worklist.push(keep);
        true
    }

    fn record_rule(&mut self, rule: &str) {
        *self.rules_fired.entry(rule.to_string()).or_insert(0) += 1;
    }

    /// Restore congruence closure and constant-lattice invariants across all E-Classes.
    pub fn rebuild(&mut self) {
        while !self.worklist.is_empty() {
            let drained: Vec<EClassId> = std::mem::take(&mut self.worklist);
            let todo: Vec<EClassId> = drained.into_iter().map(|c| self.find(c)).collect();
            for cid in todo {
                let parents = match self.classes.get(&cid) {
                    Some(c) => c.parents.clone(),
                    None => continue,
                };
                let mut new_parents = Vec::new();
                for (pnode, pclass) in parents {
                    self.memo.remove(&pnode);
                    let canon = pnode.canonicalize(|c| self.find(c));
                    let pclass_root = self.find(pclass);
                    if let Some(&existing) = self.memo.get(&canon) {
                        let existing_root = self.find(existing);
                        if existing_root != pclass_root {
                            self.union(existing_root, pclass_root);
                        }
                    } else {
                        self.memo.insert(canon.clone(), pclass_root);
                    }
                    new_parents.push((canon, pclass_root));
                }
                if let Some(c) = self.classes.get_mut(&cid) {
                    c.parents = new_parents;
                }
            }
        }

        // Canonicalize node sets inside each active E-Class
        let class_ids: Vec<EClassId> = self.classes.keys().copied().collect();
        for cid in class_ids {
            let root = self.find(cid);
            let canon_nodes = self.classes.get(&root).map(|c| {
                c.nodes
                    .iter()
                    .map(|n| n.canonicalize(|x| self.find(x)))
                    .collect::<BTreeSet<ENode>>()
            });
            if let (Some(c), Some(cn)) = (self.classes.get_mut(&root), canon_nodes) {
                c.nodes = cn;
            }
        }

        // Constant-folding analysis pass over E-Classes
        let mut const_discoveries: Vec<(EClassId, ENode)> = Vec::new();
        for (&cid, eclass) in &self.classes {
            for node in &eclass.nodes {
                if let Some(folded) = self.try_eval_const_node(node) {
                    const_discoveries.push((cid, folded));
                }
            }
        }
        for (cid, lit_node) in const_discoveries {
            let lit_id = self.add(lit_node);
            if self.union(cid, lit_id) {
                self.record_rule("const-fold");
            }
        }
    }

    fn const_of(&self, id: EClassId) -> Option<ConstDatum> {
        let root = self.find(id);
        self.classes.get(&root).and_then(|c| c.const_val.clone())
    }

    fn try_eval_const_node(&self, node: &ENode) -> Option<ENode> {
        match node {
            ENode::Unary { op, arg } => match (op, self.const_of(*arg)?) {
                (EUnaryOp::Neg, ConstDatum::Int(v)) => Some(ENode::Int(v.wrapping_neg())),
                (EUnaryOp::Neg, ConstDatum::Float(f)) => {
                    let r = -f;
                    Some(ENode::FloatBits((if r == 0.0 { 0.0 } else { r }).to_bits()))
                }
                (EUnaryOp::Not, ConstDatum::Bool(b)) => Some(ENode::Bool(!b)),
                _ => None,
            },
            ENode::Binary { op, left, right } => {
                let l = self.const_of(*left)?;
                let r = self.const_of(*right)?;
                match (op, l, r) {
                    (EBinOp::Add, ConstDatum::Int(a), ConstDatum::Int(b)) => {
                        Some(ENode::Int(a.wrapping_add(b)))
                    }
                    (EBinOp::Sub, ConstDatum::Int(a), ConstDatum::Int(b)) => {
                        Some(ENode::Int(a.wrapping_sub(b)))
                    }
                    (EBinOp::Mul, ConstDatum::Int(a), ConstDatum::Int(b)) => {
                        Some(ENode::Int(a.wrapping_mul(b)))
                    }
                    (EBinOp::Div | EBinOp::IntDiv, ConstDatum::Int(a), ConstDatum::Int(b))
                        if b != 0 =>
                    {
                        Some(ENode::Int(a.wrapping_div(b)))
                    }
                    (EBinOp::Mod, ConstDatum::Int(a), ConstDatum::Int(b)) if b != 0 => {
                        Some(ENode::Int(a.wrapping_rem(b)))
                    }
                    (EBinOp::Add, ConstDatum::Str(a), ConstDatum::Str(b)) => {
                        Some(ENode::Str(format!("{}{}", a, b)))
                    }
                    (EBinOp::Eq, ConstDatum::Int(a), ConstDatum::Int(b)) => {
                        Some(ENode::Bool(a == b))
                    }
                    (EBinOp::Ne, ConstDatum::Int(a), ConstDatum::Int(b)) => {
                        Some(ENode::Bool(a != b))
                    }
                    (EBinOp::Lt, ConstDatum::Int(a), ConstDatum::Int(b)) => {
                        Some(ENode::Bool(a < b))
                    }
                    (EBinOp::Le, ConstDatum::Int(a), ConstDatum::Int(b)) => {
                        Some(ENode::Bool(a <= b))
                    }
                    (EBinOp::Gt, ConstDatum::Int(a), ConstDatum::Int(b)) => {
                        Some(ENode::Bool(a > b))
                    }
                    (EBinOp::Ge, ConstDatum::Int(a), ConstDatum::Int(b)) => {
                        Some(ENode::Bool(a >= b))
                    }
                    (EBinOp::Eq, ConstDatum::Bool(a), ConstDatum::Bool(b)) => {
                        Some(ENode::Bool(a == b))
                    }
                    (EBinOp::Ne, ConstDatum::Bool(a), ConstDatum::Bool(b)) => {
                        Some(ENode::Bool(a != b))
                    }
                    (EBinOp::And, ConstDatum::Bool(a), ConstDatum::Bool(b)) => {
                        Some(ENode::Bool(a && b))
                    }
                    (EBinOp::Or, ConstDatum::Bool(a), ConstDatum::Bool(b)) => {
                        Some(ENode::Bool(a || b))
                    }
                    (EBinOp::Eq, ConstDatum::Str(a), ConstDatum::Str(b)) => {
                        Some(ENode::Bool(a == b))
                    }
                    (EBinOp::Ne, ConstDatum::Str(a), ConstDatum::Str(b)) => {
                        Some(ENode::Bool(a != b))
                    }
                    _ => None,
                }
            }
            ENode::Min(a, b) => match (self.const_of(*a)?, self.const_of(*b)?) {
                (ConstDatum::Int(x), ConstDatum::Int(y)) => Some(ENode::Int(x.min(y))),
                _ => None,
            },
            ENode::Max(a, b) => match (self.const_of(*a)?, self.const_of(*b)?) {
                (ConstDatum::Int(x), ConstDatum::Int(y)) => Some(ENode::Int(x.max(y))),
                _ => None,
            },
            ENode::Abs(a) => match self.const_of(*a)? {
                ConstDatum::Int(x) => x.checked_abs().map(ENode::Int),
                _ => None,
            },
            ENode::Upper(a) => match self.const_of(*a)? {
                ConstDatum::Str(s) => Some(ENode::Str(s.to_uppercase())),
                _ => None,
            },
            ENode::Lower(a) => match self.const_of(*a)? {
                ConstDatum::Str(s) => Some(ENode::Str(s.to_lowercase())),
                _ => None,
            },
            ENode::ToStr(a) => match self.const_of(*a)? {
                ConstDatum::Int(v) => Some(ENode::Str(v.to_string())),
                ConstDatum::Bool(b) => Some(ENode::Str(b.to_string())),
                ConstDatum::Str(s) => Some(ENode::Str(s)),
                _ => None,
            },
            ENode::Len(a) => {
                let root = self.find(*a);
                let cls = self.classes.get(&root)?;
                for n in &cls.nodes {
                    match n {
                        ENode::List(items) => return Some(ENode::Int(items.len() as i64)),
                        ENode::Str(s) => return Some(ENode::Int(s.chars().count() as i64)),
                        _ => {}
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Run Equality Saturation across all E-Classes until fixed point or budget.
    pub fn saturate(&mut self, max_iters: usize, max_enodes: usize) {
        self.rebuild();
        for iter in 0..max_iters {
            if self.total_enodes() > max_enodes {
                break;
            }
            let unions_before = self.total_unions;
            let nodes_before = self.total_enodes();

            let snapshot: Vec<(EClassId, Vec<ENode>)> = self
                .classes
                .iter()
                .map(|(&cid, cls)| (cid, cls.nodes.iter().cloned().collect()))
                .collect();

            let mut pending_merges: Vec<(EClassId, EClassId, &'static str)> = Vec::new();

            for (cid, nodes) in &snapshot {
                let cid = self.find(*cid);
                for node in nodes {
                    match node {
                        ENode::Unary {
                            op: EUnaryOp::Neg,
                            arg,
                        } => {
                            let arg_root = self.find(*arg);
                            if let Some(acls) = self.classes.get(&arg_root) {
                                for anode in &acls.nodes {
                                    if let ENode::Unary {
                                        op: EUnaryOp::Neg,
                                        arg: inner,
                                    } = anode
                                    {
                                        pending_merges.push((cid, *inner, "double-neg"));
                                    }
                                }
                            }
                        }
                        ENode::Unary {
                            op: EUnaryOp::Not,
                            arg,
                        } => {
                            let arg_root = self.find(*arg);
                            if let Some(acls) = self.classes.get(&arg_root).cloned() {
                                for anode in &acls.nodes {
                                    match anode {
                                        ENode::Unary {
                                            op: EUnaryOp::Not,
                                            arg: inner,
                                        } => {
                                            pending_merges.push((cid, *inner, "double-not"));
                                        }
                                        ENode::Binary { op, left, right } => {
                                            let dual = match op {
                                                EBinOp::Lt => Some(EBinOp::Ge),
                                                EBinOp::Le => Some(EBinOp::Gt),
                                                EBinOp::Gt => Some(EBinOp::Le),
                                                EBinOp::Ge => Some(EBinOp::Lt),
                                                EBinOp::Eq => Some(EBinOp::Ne),
                                                EBinOp::Ne => Some(EBinOp::Eq),
                                                _ => None,
                                            };
                                            if let Some(dop) = dual {
                                                let d_id = self.add(ENode::Binary {
                                                    op: dop,
                                                    left: *left,
                                                    right: *right,
                                                });
                                                pending_merges.push((cid, d_id, "demorgan-cmp"));
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                        }
                        ENode::Binary { op, left, right } => {
                            let l = self.find(*left);
                            let r = self.find(*right);
                            let l_const = self.const_of(l);
                            let r_const = self.const_of(r);

                            match op {
                                EBinOp::Add => {
                                    let comm = self.add(ENode::Binary {
                                        op: EBinOp::Add,
                                        left: r,
                                        right: l,
                                    });
                                    pending_merges.push((cid, comm, "comm-add"));

                                    if matches!(r_const, Some(ConstDatum::Int(0))) {
                                        pending_merges.push((cid, l, "add-zero"));
                                    }
                                    if matches!(l_const, Some(ConstDatum::Int(0))) {
                                        pending_merges.push((cid, r, "add-zero"));
                                    }
                                    if l == r {
                                        let two = self.add(ENode::Int(2));
                                        let mul2 = self.add(ENode::Binary {
                                            op: EBinOp::Mul,
                                            left: l,
                                            right: two,
                                        });
                                        pending_merges.push((cid, mul2, "add-self-to-mul2"));
                                    }

                                    // Inspect left child for (x + c1) + c2, (x - y) + y, (x * y) + (x * z)
                                    if let Some(lcls) = self.classes.get(&l).cloned() {
                                        for lnode in &lcls.nodes {
                                            match lnode {
                                                ENode::Binary {
                                                    op: EBinOp::Sub,
                                                    left: x,
                                                    right: y,
                                                } if self.find(*y) == r => {
                                                    pending_merges.push((cid, *x, "cancel-sub-add"));
                                                }
                                                ENode::Binary {
                                                    op: EBinOp::Add,
                                                    left: x,
                                                    right: c1,
                                                } => {
                                                    if let (
                                                        Some(ConstDatum::Int(v1)),
                                                        Some(ConstDatum::Int(v2)),
                                                    ) = (self.const_of(*c1), r_const.clone())
                                                    {
                                                        let c_sum =
                                                            self.add(ENode::Int(v1.wrapping_add(v2)));
                                                        let reassoc = self.add(ENode::Binary {
                                                            op: EBinOp::Add,
                                                            left: *x,
                                                            right: c_sum,
                                                        });
                                                        pending_merges.push((
                                                            cid,
                                                            reassoc,
                                                            "reassoc-add-const",
                                                        ));
                                                    }
                                                }
                                                ENode::Binary {
                                                    op: EBinOp::Sub,
                                                    left: x,
                                                    right: c1,
                                                } => {
                                                    if let (
                                                        Some(ConstDatum::Int(v1)),
                                                        Some(ConstDatum::Int(v2)),
                                                    ) = (self.const_of(*c1), r_const.clone())
                                                    {
                                                        let diff = v2.wrapping_sub(v1);
                                                        let c_node = self.add(ENode::Int(diff));
                                                        let reassoc = self.add(ENode::Binary {
                                                            op: EBinOp::Add,
                                                            left: *x,
                                                            right: c_node,
                                                        });
                                                        pending_merges.push((
                                                            cid,
                                                            reassoc,
                                                            "reassoc-sub-add-const",
                                                        ));
                                                    }
                                                }
                                                ENode::Binary {
                                                    op: EBinOp::Mul,
                                                    left: a1,
                                                    right: b1,
                                                } => {
                                                    if let Some(rcls) = self.classes.get(&r).cloned()
                                                    {
                                                        for rnode in &rcls.nodes {
                                                            if let ENode::Binary {
                                                                op: EBinOp::Mul,
                                                                left: a2,
                                                                right: b2,
                                                            } = rnode
                                                            {
                                                                if self.find(*a1) == self.find(*a2) {
                                                                    let sum_b =
                                                                        self.add(ENode::Binary {
                                                                            op: EBinOp::Add,
                                                                            left: *b1,
                                                                            right: *b2,
                                                                        });
                                                                    let factored =
                                                                        self.add(ENode::Binary {
                                                                            op: EBinOp::Mul,
                                                                            left: *a1,
                                                                            right: sum_b,
                                                                        });
                                                                    pending_merges.push((
                                                                        cid,
                                                                        factored,
                                                                        "factor-dist-add",
                                                                    ));
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                    }

                                    // x + (-y) => x - y
                                    if let Some(rcls) = self.classes.get(&r).cloned() {
                                        for rnode in &rcls.nodes {
                                            if let ENode::Unary {
                                                op: EUnaryOp::Neg,
                                                arg: y,
                                            } = rnode
                                            {
                                                let sub_id = self.add(ENode::Binary {
                                                    op: EBinOp::Sub,
                                                    left: l,
                                                    right: *y,
                                                });
                                                pending_merges
                                                    .push((cid, sub_id, "add-neg-to-sub"));
                                            }
                                        }
                                    }
                                }
                                EBinOp::Sub => {
                                    if matches!(r_const, Some(ConstDatum::Int(0))) {
                                        pending_merges.push((cid, l, "sub-zero"));
                                    }
                                    if l == r {
                                        let zero = self.add(ENode::Int(0));
                                        pending_merges.push((cid, zero, "sub-self"));
                                    }

                                    // (x + y) - y => x, (x + c1) - c2 => x + (c1 - c2)
                                    if let Some(lcls) = self.classes.get(&l).cloned() {
                                        for lnode in &lcls.nodes {
                                            match lnode {
                                                ENode::Binary {
                                                    op: EBinOp::Add,
                                                    left: x,
                                                    right: y,
                                                } => {
                                                    if self.find(*y) == r {
                                                        pending_merges
                                                            .push((cid, *x, "cancel-add-sub"));
                                                    }
                                                    if self.find(*x) == r {
                                                        pending_merges
                                                            .push((cid, *y, "cancel-add-sub"));
                                                    }
                                                    if let (
                                                        Some(ConstDatum::Int(v1)),
                                                        Some(ConstDatum::Int(v2)),
                                                    ) = (self.const_of(*y), r_const.clone())
                                                    {
                                                        let diff = v1.wrapping_sub(v2);
                                                        let c_node = self.add(ENode::Int(diff));
                                                        let reassoc = self.add(ENode::Binary {
                                                            op: EBinOp::Add,
                                                            left: *x,
                                                            right: c_node,
                                                        });
                                                        pending_merges.push((
                                                            cid,
                                                            reassoc,
                                                            "reassoc-add-sub-const",
                                                        ));
                                                    }
                                                }
                                                ENode::Binary {
                                                    op: EBinOp::Sub,
                                                    left: x,
                                                    right: c1,
                                                } => {
                                                    if let (
                                                        Some(ConstDatum::Int(v1)),
                                                        Some(ConstDatum::Int(v2)),
                                                    ) = (self.const_of(*c1), r_const.clone())
                                                    {
                                                        let sum = v1.wrapping_add(v2);
                                                        let c_node = self.add(ENode::Int(sum));
                                                        let reassoc = self.add(ENode::Binary {
                                                            op: EBinOp::Sub,
                                                            left: *x,
                                                            right: c_node,
                                                        });
                                                        pending_merges.push((
                                                            cid,
                                                            reassoc,
                                                            "reassoc-sub-sub-const",
                                                        ));
                                                    }
                                                }
                                                _ => {}
                                            }
                                        }
                                    }

                                    // x - (-y) => x + y
                                    if let Some(rcls) = self.classes.get(&r).cloned() {
                                        for rnode in &rcls.nodes {
                                            if let ENode::Unary {
                                                op: EUnaryOp::Neg,
                                                arg: y,
                                            } = rnode
                                            {
                                                let add_id = self.add(ENode::Binary {
                                                    op: EBinOp::Add,
                                                    left: l,
                                                    right: *y,
                                                });
                                                pending_merges
                                                    .push((cid, add_id, "sub-neg-to-add"));
                                            }
                                        }
                                    }
                                }
                                EBinOp::Mul => {
                                    let comm = self.add(ENode::Binary {
                                        op: EBinOp::Mul,
                                        left: r,
                                        right: l,
                                    });
                                    pending_merges.push((cid, comm, "comm-mul"));

                                    if matches!(r_const, Some(ConstDatum::Int(1))) {
                                        pending_merges.push((cid, l, "mul-one"));
                                    }
                                    if matches!(l_const, Some(ConstDatum::Int(1))) {
                                        pending_merges.push((cid, r, "mul-one"));
                                    }
                                    if matches!(r_const, Some(ConstDatum::Int(0)))
                                        || matches!(l_const, Some(ConstDatum::Int(0)))
                                    {
                                        let zero = self.add(ENode::Int(0));
                                        pending_merges.push((cid, zero, "mul-zero"));
                                    }
                                    if matches!(r_const, Some(ConstDatum::Int(2))) {
                                        let add_self = self.add(ENode::Binary {
                                            op: EBinOp::Add,
                                            left: l,
                                            right: l,
                                        });
                                        pending_merges.push((cid, add_self, "strength-reduce-mul2"));
                                    }
                                    if let Some(lcls) = self.classes.get(&l).cloned() {
                                        for lnode in &lcls.nodes {
                                            if let ENode::Binary {
                                                op: EBinOp::Mul,
                                                left: x,
                                                right: c1,
                                            } = lnode
                                            {
                                                if let (
                                                    Some(ConstDatum::Int(v1)),
                                                    Some(ConstDatum::Int(v2)),
                                                ) = (self.const_of(*c1), r_const.clone())
                                                {
                                                    let prod = self.add(ENode::Int(v1.wrapping_mul(v2)));
                                                    let reassoc = self.add(ENode::Binary {
                                                        op: EBinOp::Mul,
                                                        left: *x,
                                                        right: prod,
                                                    });
                                                    pending_merges
                                                        .push((cid, reassoc, "reassoc-mul-const"));
                                                }
                                            }
                                        }
                                    }
                                }
                                EBinOp::Div | EBinOp::IntDiv => {
                                    if matches!(r_const, Some(ConstDatum::Int(1))) {
                                        pending_merges.push((cid, l, "div-one"));
                                    }
                                    if let Some(ConstDatum::Int(rv)) = r_const {
                                        if rv != 0 {
                                            if let Some(lcls) = self.classes.get(&l).cloned() {
                                                for lnode in &lcls.nodes {
                                                    if let ENode::Binary {
                                                        op: EBinOp::Mul,
                                                        left: x,
                                                        right: c1,
                                                    } = lnode
                                                    {
                                                        if self.const_of(*c1)
                                                            == Some(ConstDatum::Int(rv))
                                                        {
                                                            pending_merges
                                                                .push((cid, *x, "mul-div-cancel"));
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                EBinOp::Mod => {
                                    if matches!(r_const, Some(ConstDatum::Int(1))) {
                                        let zero = self.add(ENode::Int(0));
                                        pending_merges.push((cid, zero, "mod-one"));
                                    }
                                }
                                EBinOp::Eq => {
                                    let comm = self.add(ENode::Binary {
                                        op: EBinOp::Eq,
                                        left: r,
                                        right: l,
                                    });
                                    pending_merges.push((cid, comm, "comm-eq"));
                                    if l == r {
                                        let t = self.add(ENode::Bool(true));
                                        pending_merges.push((cid, t, "refl-eq"));
                                    }
                                }
                                EBinOp::Ne => {
                                    let comm = self.add(ENode::Binary {
                                        op: EBinOp::Ne,
                                        left: r,
                                        right: l,
                                    });
                                    pending_merges.push((cid, comm, "comm-ne"));
                                    if l == r {
                                        let f = self.add(ENode::Bool(false));
                                        pending_merges.push((cid, f, "refl-ne"));
                                    }
                                }
                                EBinOp::Lt | EBinOp::Gt => {
                                    if l == r {
                                        let f = self.add(ENode::Bool(false));
                                        pending_merges.push((cid, f, "irrefl-lt-gt"));
                                    }
                                }
                                EBinOp::Le | EBinOp::Ge => {
                                    if l == r {
                                        let t = self.add(ENode::Bool(true));
                                        pending_merges.push((cid, t, "refl-le-ge"));
                                    }
                                }
                                EBinOp::And => {
                                    if l == r {
                                        pending_merges.push((cid, l, "idemp-and"));
                                    }
                                    if matches!(r_const, Some(ConstDatum::Bool(true))) {
                                        pending_merges.push((cid, l, "and-true"));
                                    }
                                    if matches!(l_const, Some(ConstDatum::Bool(true))) {
                                        pending_merges.push((cid, r, "and-true"));
                                    }
                                    if matches!(r_const, Some(ConstDatum::Bool(false)))
                                        || matches!(l_const, Some(ConstDatum::Bool(false)))
                                    {
                                        let f = self.add(ENode::Bool(false));
                                        pending_merges.push((cid, f, "and-false"));
                                    }
                                }
                                EBinOp::Or => {
                                    if l == r {
                                        pending_merges.push((cid, l, "idemp-or"));
                                    }
                                    if matches!(r_const, Some(ConstDatum::Bool(false))) {
                                        pending_merges.push((cid, l, "or-false"));
                                    }
                                    if matches!(l_const, Some(ConstDatum::Bool(false))) {
                                        pending_merges.push((cid, r, "or-false"));
                                    }
                                    if matches!(r_const, Some(ConstDatum::Bool(true)))
                                        || matches!(l_const, Some(ConstDatum::Bool(true)))
                                    {
                                        let t = self.add(ENode::Bool(true));
                                        pending_merges.push((cid, t, "or-true"));
                                    }
                                }
                            }
                        }
                        ENode::Min(a, b) => {
                            let la = self.find(*a);
                            let rb = self.find(*b);
                            let comm = self.add(ENode::Min(rb, la));
                            pending_merges.push((cid, comm, "comm-min"));
                            if la == rb {
                                pending_merges.push((cid, la, "idemp-min"));
                            }
                            if let Some(bcls) = self.classes.get(&rb).cloned() {
                                for bnode in &bcls.nodes {
                                    if let ENode::Max(x, _) = bnode {
                                        if self.find(*x) == la {
                                            pending_merges.push((cid, la, "absorb-min-max"));
                                        }
                                    }
                                }
                            }
                        }
                        ENode::Max(a, b) => {
                            let la = self.find(*a);
                            let rb = self.find(*b);
                            let comm = self.add(ENode::Max(rb, la));
                            pending_merges.push((cid, comm, "comm-max"));
                            if la == rb {
                                pending_merges.push((cid, la, "idemp-max"));
                            }
                            if let Some(bcls) = self.classes.get(&rb).cloned() {
                                for bnode in &bcls.nodes {
                                    if let ENode::Min(x, _) = bnode {
                                        if self.find(*x) == la {
                                            pending_merges.push((cid, la, "absorb-max-min"));
                                        }
                                    }
                                }
                            }
                        }
                        ENode::Abs(a) => {
                            let ra = self.find(*a);
                            if let Some(acls) = self.classes.get(&ra).cloned() {
                                for anode in &acls.nodes {
                                    match anode {
                                        ENode::Abs(_) => {
                                            pending_merges.push((cid, ra, "idemp-abs"));
                                        }
                                        ENode::Unary {
                                            op: EUnaryOp::Neg,
                                            arg: inner,
                                        } => {
                                            let abs_inner = self.add(ENode::Abs(*inner));
                                            pending_merges.push((cid, abs_inner, "abs-neg"));
                                        }
                                        _ => {}
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }

            for (c1, c2, rule_name) in pending_merges {
                if self.union(c1, c2) {
                    self.record_rule(rule_name);
                }
            }

            self.rebuild();
            self.iterations = iter + 1;

            if self.total_unions == unions_before && self.total_enodes() == nodes_before {
                break;
            }
        }
    }

    /// Compute bottom-up minimum gas cost and winning ENode for every E-Class.
    pub fn compute_best_costs(&self) -> BTreeMap<EClassId, (u64, ENode)> {
        let mut best: BTreeMap<EClassId, (u64, ENode)> = BTreeMap::new();
        let mut changed = true;
        while changed {
            changed = false;
            for (&cid, eclass) in &self.classes {
                let root = self.find(cid);
                for node in &eclass.nodes {
                    let mut all_ready = true;
                    let mut cost = node.base_cost();
                    for child in node.children() {
                        let croot = self.find(child);
                        if let Some((ccost, _)) = best.get(&croot) {
                            cost = cost.saturating_add(*ccost);
                        } else {
                            all_ready = false;
                            break;
                        }
                    }
                    if all_ready {
                        let update = match best.get(&root) {
                            None => true,
                            Some((prev_cost, _)) => cost < *prev_cost,
                        };
                        if update {
                            best.insert(root, (cost, node.clone()));
                            changed = true;
                        }
                    }
                }
            }
        }
        best
    }

    pub fn extract_expr(
        &self,
        id: EClassId,
        best: &BTreeMap<EClassId, (u64, ENode)>,
        fallback: &Expr,
    ) -> (Expr, u64) {
        let mut visited = BTreeSet::new();
        match self.extract_rec(self.find(id), best, &mut visited) {
            Some((e, c)) => (e, c),
            None => (fallback.clone(), expr_gas_cost(fallback)),
        }
    }

    fn extract_rec(
        &self,
        id: EClassId,
        best: &BTreeMap<EClassId, (u64, ENode)>,
        visiting: &mut BTreeSet<EClassId>,
    ) -> Option<(Expr, u64)> {
        let root = self.find(id);
        if !visiting.insert(root) {
            return None;
        }
        let (cost, node) = best.get(&root)?;
        let expr = match node {
            ENode::Int(v) => Expr::Int(*v),
            ENode::FloatBits(b) => Expr::Float(f64::from_bits(*b)),
            ENode::Bool(b) => Expr::Bool(*b),
            ENode::Str(s) => Expr::Str(s.clone()),
            ENode::Var(v) => Expr::Var(v.clone()),
            ENode::EnumVariant { enum_name, variant } => Expr::EnumVariant {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
            },
            ENode::List(items) => {
                let mut out = Vec::with_capacity(items.len());
                for &c in items {
                    out.push(self.extract_rec(c, best, visiting)?.0);
                }
                Expr::List(out)
            }
            ENode::StructInit { name, fields } => {
                let mut out = Vec::with_capacity(fields.len());
                for (k, c) in fields {
                    out.push((k.clone(), self.extract_rec(*c, best, visiting)?.0));
                }
                Expr::StructInit {
                    name: name.clone(),
                    fields: out,
                }
            }
            ENode::FieldAccess { base, field } => Expr::FieldAccess {
                base: Box::new(self.extract_rec(*base, best, visiting)?.0),
                field: field.clone(),
            },
            ENode::Index { base, index } => Expr::Index {
                base: Box::new(self.extract_rec(*base, best, visiting)?.0),
                index: Box::new(self.extract_rec(*index, best, visiting)?.0),
            },
            ENode::Unary { op, arg } => Expr::Unary {
                op: match op {
                    EUnaryOp::Neg => UnaryOp::Neg,
                    EUnaryOp::Not => UnaryOp::Not,
                },
                expr: Box::new(self.extract_rec(*arg, best, visiting)?.0),
            },
            ENode::Binary { op, left, right } => Expr::Binary {
                op: match op {
                    EBinOp::Add => BinOp::Add,
                    EBinOp::Sub => BinOp::Sub,
                    EBinOp::Mul => BinOp::Mul,
                    EBinOp::Div => BinOp::Div,
                    EBinOp::IntDiv => BinOp::IntDiv,
                    EBinOp::Mod => BinOp::Mod,
                    EBinOp::Eq => BinOp::Eq,
                    EBinOp::Ne => BinOp::Ne,
                    EBinOp::Lt => BinOp::Lt,
                    EBinOp::Le => BinOp::Le,
                    EBinOp::Gt => BinOp::Gt,
                    EBinOp::Ge => BinOp::Ge,
                    EBinOp::And => BinOp::And,
                    EBinOp::Or => BinOp::Or,
                },
                left: Box::new(self.extract_rec(*left, best, visiting)?.0),
                right: Box::new(self.extract_rec(*right, best, visiting)?.0),
            },
            ENode::Call { func, args } => {
                let mut out = Vec::with_capacity(args.len());
                for &c in args {
                    out.push(self.extract_rec(c, best, visiting)?.0);
                }
                Expr::Call {
                    func: func.clone(),
                    args: out,
                }
            }
            ENode::Len(a) => Expr::intrinsic(Intrinsic::Len(
                self.extract_rec(*a, best, visiting)?.0,
            )),
            ENode::Min(a, b) => Expr::intrinsic(Intrinsic::Min(
                self.extract_rec(*a, best, visiting)?.0,
                self.extract_rec(*b, best, visiting)?.0,
            )),
            ENode::Max(a, b) => Expr::intrinsic(Intrinsic::Max(
                self.extract_rec(*a, best, visiting)?.0,
                self.extract_rec(*b, best, visiting)?.0,
            )),
            ENode::Abs(a) => Expr::intrinsic(Intrinsic::Abs(
                self.extract_rec(*a, best, visiting)?.0,
            )),
            ENode::Push { list, value } => Expr::intrinsic(Intrinsic::Push {
                list: self.extract_rec(*list, best, visiting)?.0,
                value: self.extract_rec(*value, best, visiting)?.0,
            }),
            ENode::Print(args) => {
                let mut out = Vec::with_capacity(args.len());
                for &c in args {
                    out.push(self.extract_rec(c, best, visiting)?.0);
                }
                Expr::intrinsic(Intrinsic::Print(out))
            }
            ENode::Contains { haystack, needle } => Expr::intrinsic(Intrinsic::Contains {
                haystack: self.extract_rec(*haystack, best, visiting)?.0,
                needle: self.extract_rec(*needle, best, visiting)?.0,
            }),
            ENode::Upper(a) => Expr::intrinsic(Intrinsic::Upper(
                self.extract_rec(*a, best, visiting)?.0,
            )),
            ENode::Lower(a) => Expr::intrinsic(Intrinsic::Lower(
                self.extract_rec(*a, best, visiting)?.0,
            )),
            ENode::ToStr(a) => Expr::intrinsic(Intrinsic::ToStr(
                self.extract_rec(*a, best, visiting)?.0,
            )),
        };
        visiting.remove(&root);
        Some((expr, *cost))
    }
}

pub fn expr_gas_cost(expr: &Expr) -> u64 {
    match expr {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Bool(_)
        | Expr::Str(_)
        | Expr::Var(_)
        | Expr::EnumVariant { .. } => 1,
        Expr::Unary { expr: inner, .. } => 1 + expr_gas_cost(inner),
        Expr::Binary { op, left, right } => {
            let base = match op {
                BinOp::Add
                | BinOp::Sub
                | BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or => 2,
                BinOp::Mul => 4,
                BinOp::Div | BinOp::IntDiv | BinOp::Mod => 8,
            };
            base + expr_gas_cost(left) + expr_gas_cost(right)
        }
        Expr::FieldAccess { base, .. } => 3 + expr_gas_cost(base),
        Expr::Index { base, index } => 3 + expr_gas_cost(base) + expr_gas_cost(index),
        Expr::List(items) => 5 + items.iter().map(expr_gas_cost).sum::<u64>(),
        Expr::StructInit { fields, .. } => {
            5 + fields.iter().map(|(_, v)| expr_gas_cost(v)).sum::<u64>()
        }
        Expr::Call { args, .. } => 5 + args.iter().map(expr_gas_cost).sum::<u64>(),
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(a)
            | Intrinsic::Abs(a)
            | Intrinsic::Upper(a)
            | Intrinsic::Lower(a)
            | Intrinsic::ToStr(a) => 3 + expr_gas_cost(a),
            Intrinsic::Min(a, b) | Intrinsic::Max(a, b) => 3 + expr_gas_cost(a) + expr_gas_cost(b),
            Intrinsic::Push { list, value } => 5 + expr_gas_cost(list) + expr_gas_cost(value),
            Intrinsic::Contains { haystack, needle } => {
                5 + expr_gas_cost(haystack) + expr_gas_cost(needle)
            }
            Intrinsic::Print(args) => 5 + args.iter().map(expr_gas_cost).sum::<u64>(),
        },
    }
}

pub fn format_expr_compact(expr: &Expr) -> String {
    match expr {
        Expr::Int(v) => v.to_string(),
        Expr::Float(f) => format!("{}", f),
        Expr::Bool(b) => b.to_string(),
        Expr::Str(s) => format!("{:?}", s),
        Expr::Var(v) => v.clone(),
        Expr::EnumVariant { enum_name, variant } => format!("{}::{}", enum_name, variant),
        Expr::List(items) => {
            let parts: Vec<String> = items.iter().map(format_expr_compact).collect();
            format!("[{}]", parts.join(", "))
        }
        Expr::StructInit { name, fields } => {
            let parts: Vec<String> = fields
                .iter()
                .map(|(k, v)| format!("{}: {}", k, format_expr_compact(v)))
                .collect();
            format!("{}{{ {} }}", name, parts.join(", "))
        }
        Expr::FieldAccess { base, field } => format!("{}.{}", format_expr_compact(base), field),
        Expr::Index { base, index } => {
            format!("{}[{}]", format_expr_compact(base), format_expr_compact(index))
        }
        Expr::Unary { op, expr: inner } => match op {
            UnaryOp::Neg => format!("-({})", format_expr_compact(inner)),
            UnaryOp::Not => format!("!({})", format_expr_compact(inner)),
        },
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
                BinOp::And => "&&",
                BinOp::Or => "||",
            };
            format!(
                "({} {} {})",
                format_expr_compact(left),
                sym,
                format_expr_compact(right)
            )
        }
        Expr::Call { func, args } => {
            let parts: Vec<String> = args.iter().map(format_expr_compact).collect();
            format!("{}({})", func, parts.join(", "))
        }
        Expr::Intrinsic(intr) => match intr.as_ref() {
            Intrinsic::Len(a) => format!("len({})", format_expr_compact(a)),
            Intrinsic::Min(a, b) => {
                format!("min({}, {})", format_expr_compact(a), format_expr_compact(b))
            }
            Intrinsic::Max(a, b) => {
                format!("max({}, {})", format_expr_compact(a), format_expr_compact(b))
            }
            Intrinsic::Abs(a) => format!("abs({})", format_expr_compact(a)),
            Intrinsic::Push { list, value } => {
                format!("push({}, {})", format_expr_compact(list), format_expr_compact(value))
            }
            Intrinsic::Print(args) => {
                let parts: Vec<String> = args.iter().map(format_expr_compact).collect();
                format!("print({})", parts.join(", "))
            }
            Intrinsic::Contains { haystack, needle } => format!(
                "contains({}, {})",
                format_expr_compact(haystack),
                format_expr_compact(needle)
            ),
            Intrinsic::Upper(a) => format!("upper({})", format_expr_compact(a)),
            Intrinsic::Lower(a) => format!("lower({})", format_expr_compact(a)),
            Intrinsic::ToStr(a) => format!("to_str({})", format_expr_compact(a)),
        },
    }
}

#[derive(Debug, Clone)]
pub struct EGraphRewriteWitness {
    pub scope: String,
    pub eclass_id: EClassId,
    pub before_expr: String,
    pub after_expr: String,
    pub cost_before: u64,
    pub cost_after: u64,
    pub class_size: usize,
}

#[derive(Debug, Clone)]
pub struct EGraphReport {
    pub total_eclasses: usize,
    pub total_enodes: usize,
    pub total_unions: usize,
    pub saturation_iterations: usize,
    pub expressions_optimized: usize,
    pub dead_branches_pruned: usize,
    pub cost_before: u64,
    pub cost_after: u64,
    pub gas_saved: u64,
    pub translation_validated: bool,
    pub rules_fired: BTreeMap<String, usize>,
    pub rewrites: Vec<EGraphRewriteWitness>,
    pub mermaid: String,
    pub views_by_spoke: BTreeMap<String, String>,
    pub optimized_hub: HubModule,
    pub elapsed_ms: u128,
}

#[derive(Debug, Clone)]
pub struct SpecializationSite {
    pub caller: String,
    pub callee: String,
    pub specialized_name: String,
    pub static_bindings: String,
    pub summary: String,
}

#[derive(Debug, Clone)]
pub struct PartialEvalReport {
    pub specialized_calls: usize,
    pub residual_functions_synthesized: usize,
    pub static_branches_folded: usize,
    pub loops_unrolled: usize,
    pub egraph_rewrites: usize,
    pub nodes_before: usize,
    pub nodes_after: usize,
    pub vm_steps_before: usize,
    pub vm_steps_after: usize,
    pub gas_before: u64,
    pub gas_after: u64,
    pub translation_validated: bool,
    pub stdout_before: String,
    pub stdout_after: String,
    pub tests_passed: usize,
    pub tests_total: usize,
    pub specializations: Vec<SpecializationSite>,
    pub views_by_spoke: BTreeMap<String, String>,
    pub residual_hub: HubModule,
    pub elapsed_ms: u128,
}

/// Run Equality Saturation & Congruence-Closure E-Graph Superoptimization across `hub`.
pub fn superoptimize_egraph(hub: &HubModule) -> EGraphReport {
    let start = Instant::now();
    let mut eg = EGraph::new();

    // 1. Seed the E-Graph with all expressions in the module
    for item in &hub.items {
        match item {
            Item::Function(f) => seed_stmts_in_egraph(&mut eg, &f.body),
            Item::Test(t) => seed_stmts_in_egraph(&mut eg, &t.body),
            _ => {}
        }
    }

    // 2. Run Equality Saturation & Congruence Closure
    eg.saturate(10, 4_000);
    let best = eg.compute_best_costs();

    // 3. Extract the provably minimum-cost Hub AST & record witnesses
    let mut optimized_hub = hub.clone();
    let mut rewrites = Vec::new();
    let mut cost_before = 0u64;
    let mut cost_after = 0u64;
    let mut dead_branches_pruned = 0usize;

    for item in &mut optimized_hub.items {
        match item {
            Item::Function(f) => {
                let scope = format!("fn {}", f.name);
                f.body = extract_stmts_from_egraph(
                    &f.body,
                    &mut eg,
                    &best,
                    &scope,
                    &mut rewrites,
                    &mut cost_before,
                    &mut cost_after,
                    &mut dead_branches_pruned,
                );
            }
            Item::Test(t) => {
                let scope = format!("test {}", t.name);
                t.body = extract_stmts_from_egraph(
                    &t.body,
                    &mut eg,
                    &best,
                    &scope,
                    &mut rewrites,
                    &mut cost_before,
                    &mut cost_after,
                    &mut dead_branches_pruned,
                );
            }
            _ => {}
        }
    }

    // 4. Translation Validation: verify identical VM stdout & unit test results
    let ev_before = eval_module_default(hub);
    let ev_after = eval_module_default(&optimized_hub);
    let tests_after = eval_tests_default(&optimized_hub);
    let translation_validated = ev_before.ok == ev_after.ok
        && ev_before.stdout == ev_after.stdout
        && tests_after.iter().all(|t| t.passed);

    let mermaid = render_egraph_mermaid(&eg, &best, &rewrites);

    let mut views_by_spoke = BTreeMap::new();
    for spoke in SpokeId::ALL {
        views_by_spoke.insert(spoke.as_str().to_string(), lens_for(spoke).get(&optimized_hub));
    }

    let gas_saved = cost_before.saturating_sub(cost_after);

    EGraphReport {
        total_eclasses: eg.total_eclasses(),
        total_enodes: eg.total_enodes(),
        total_unions: eg.total_unions,
        saturation_iterations: eg.iterations,
        expressions_optimized: rewrites.len(),
        dead_branches_pruned,
        cost_before,
        cost_after,
        gas_saved,
        translation_validated,
        rules_fired: eg.rules_fired,
        rewrites,
        mermaid,
        views_by_spoke,
        optimized_hub,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

fn seed_stmts_in_egraph(eg: &mut EGraph, stmts: &[Stmt]) {
    for stmt in stmts {
        match stmt {
            Stmt::Comment { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {}
            Stmt::Let { value, .. } => {
                eg.add_expr(value);
            }
            Stmt::Assign { target, value, .. } => {
                if let AssignTarget::Index { index, .. } = target {
                    eg.add_expr(index);
                }
                eg.add_expr(value);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                eg.add_expr(cond);
                seed_stmts_in_egraph(eg, then_body);
                seed_stmts_in_egraph(eg, else_body);
            }
            Stmt::Match { expr, arms, .. } => {
                eg.add_expr(expr);
                for arm in arms {
                    seed_stmts_in_egraph(eg, &arm.body);
                }
            }
            Stmt::While { cond, body, .. } => {
                eg.add_expr(cond);
                seed_stmts_in_egraph(eg, body);
            }
            Stmt::ForEach { iter, body, .. } => {
                eg.add_expr(iter);
                seed_stmts_in_egraph(eg, body);
            }
            Stmt::ForRange {
                start, end, body, ..
            } => {
                eg.add_expr(start);
                eg.add_expr(end);
                seed_stmts_in_egraph(eg, body);
            }
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    eg.add_expr(v);
                }
            }
            Stmt::Assert { cond, .. } => {
                eg.add_expr(cond);
            }
            Stmt::AssertEq { left, right, .. } => {
                eg.add_expr(left);
                eg.add_expr(right);
            }
            Stmt::Expr { expr, .. } => {
                eg.add_expr(expr);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn extract_stmts_from_egraph(
    stmts: &[Stmt],
    eg: &mut EGraph,
    best: &BTreeMap<EClassId, (u64, ENode)>,
    scope: &str,
    rewrites: &mut Vec<EGraphRewriteWitness>,
    cost_before: &mut u64,
    cost_after: &mut u64,
    dead_branches_pruned: &mut usize,
) -> Vec<Stmt> {
    let mut out = Vec::new();
    for stmt in stmts {
        if matches!(out.last(), Some(Stmt::Return { .. })) {
            break;
        }
        match stmt {
            Stmt::Comment { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {
                out.push(stmt.clone());
            }
            Stmt::Let {
                id,
                name,
                mutable,
                ty,
                value,
                meta,
            } => {
                let v = extract_and_record(value, eg, best, scope, rewrites, cost_before, cost_after);
                out.push(Stmt::Let {
                    id: *id,
                    name: name.clone(),
                    mutable: *mutable,
                    ty: ty.clone(),
                    value: v,
                    meta: meta.clone(),
                });
            }
            Stmt::Assign {
                id,
                target,
                op,
                value,
                meta,
            } => {
                let new_target = match target {
                    AssignTarget::Index { base, index } => AssignTarget::Index {
                        base: base.clone(),
                        index: extract_and_record(
                            index,
                            eg,
                            best,
                            scope,
                            rewrites,
                            cost_before,
                            cost_after,
                        ),
                    },
                    other => other.clone(),
                };
                let new_val =
                    extract_and_record(value, eg, best, scope, rewrites, cost_before, cost_after);
                // Elide no-op assignments (`x += 0`, `x -= 0`, `x = x`)
                let is_noop = match (&new_target, op, &new_val) {
                    (AssignTarget::Var(_), AssignOp::AddAssign | AssignOp::SubAssign, Expr::Int(0)) => {
                        true
                    }
                    (AssignTarget::Var(lhs), AssignOp::Set, Expr::Var(rhs)) if lhs == rhs => true,
                    _ => false,
                };
                if !is_noop {
                    out.push(Stmt::Assign {
                        id: *id,
                        target: new_target,
                        op: *op,
                        value: new_val,
                        meta: meta.clone(),
                    });
                }
            }
            Stmt::If {
                id,
                cond,
                then_body,
                else_body,
                meta,
            } => {
                let c = extract_and_record(cond, eg, best, scope, rewrites, cost_before, cost_after);
                let tb = extract_stmts_from_egraph(
                    then_body,
                    eg,
                    best,
                    scope,
                    rewrites,
                    cost_before,
                    cost_after,
                    dead_branches_pruned,
                );
                let eb = extract_stmts_from_egraph(
                    else_body,
                    eg,
                    best,
                    scope,
                    rewrites,
                    cost_before,
                    cost_after,
                    dead_branches_pruned,
                );
                match c {
                    Expr::Bool(true) => {
                        *dead_branches_pruned += 1;
                        out.extend(tb);
                    }
                    Expr::Bool(false) => {
                        *dead_branches_pruned += 1;
                        out.extend(eb);
                    }
                    _ => {
                        out.push(Stmt::If {
                            id: *id,
                            cond: c,
                            then_body: tb,
                            else_body: eb,
                            meta: meta.clone(),
                        });
                    }
                }
            }
            Stmt::Match {
                id,
                expr,
                arms,
                meta,
            } => {
                let e = extract_and_record(expr, eg, best, scope, rewrites, cost_before, cost_after);
                let mut new_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    let body = extract_stmts_from_egraph(
                        &arm.body,
                        eg,
                        best,
                        scope,
                        rewrites,
                        cost_before,
                        cost_after,
                        dead_branches_pruned,
                    );
                    new_arms.push(crate::hub::MatchArm {
                        pat: arm.pat.clone(),
                        body,
                    });
                }
                out.push(Stmt::Match {
                    id: *id,
                    expr: e,
                    arms: new_arms,
                    meta: meta.clone(),
                });
            }
            Stmt::While {
                id,
                cond,
                body,
                meta,
            } => {
                let c = extract_and_record(cond, eg, best, scope, rewrites, cost_before, cost_after);
                if matches!(c, Expr::Bool(false)) {
                    *dead_branches_pruned += 1;
                } else {
                    let b = extract_stmts_from_egraph(
                        body,
                        eg,
                        best,
                        scope,
                        rewrites,
                        cost_before,
                        cost_after,
                        dead_branches_pruned,
                    );
                    out.push(Stmt::While {
                        id: *id,
                        cond: c,
                        body: b,
                        meta: meta.clone(),
                    });
                }
            }
            Stmt::ForEach {
                id,
                var,
                iter,
                body,
                meta,
            } => {
                let it = extract_and_record(iter, eg, best, scope, rewrites, cost_before, cost_after);
                let b = extract_stmts_from_egraph(
                    body,
                    eg,
                    best,
                    scope,
                    rewrites,
                    cost_before,
                    cost_after,
                    dead_branches_pruned,
                );
                out.push(Stmt::ForEach {
                    id: *id,
                    var: var.clone(),
                    iter: it,
                    body: b,
                    meta: meta.clone(),
                });
            }
            Stmt::ForRange {
                id,
                var,
                start,
                end,
                body,
                meta,
            } => {
                let s = extract_and_record(start, eg, best, scope, rewrites, cost_before, cost_after);
                let e = extract_and_record(end, eg, best, scope, rewrites, cost_before, cost_after);
                let b = extract_stmts_from_egraph(
                    body,
                    eg,
                    best,
                    scope,
                    rewrites,
                    cost_before,
                    cost_after,
                    dead_branches_pruned,
                );
                out.push(Stmt::ForRange {
                    id: *id,
                    var: var.clone(),
                    start: s,
                    end: e,
                    body: b,
                    meta: meta.clone(),
                });
            }
            Stmt::Return { id, value, meta } => {
                let v = value
                    .as_ref()
                    .map(|expr| extract_and_record(expr, eg, best, scope, rewrites, cost_before, cost_after));
                out.push(Stmt::Return {
                    id: *id,
                    value: v,
                    meta: meta.clone(),
                });
            }
            Stmt::Assert { id, cond, meta } => {
                let c = extract_and_record(cond, eg, best, scope, rewrites, cost_before, cost_after);
                out.push(Stmt::Assert {
                    id: *id,
                    cond: c,
                    meta: meta.clone(),
                });
            }
            Stmt::AssertEq {
                id,
                left,
                right,
                meta,
            } => {
                let l = extract_and_record(left, eg, best, scope, rewrites, cost_before, cost_after);
                let r = extract_and_record(right, eg, best, scope, rewrites, cost_before, cost_after);
                out.push(Stmt::AssertEq {
                    id: *id,
                    left: l,
                    right: r,
                    meta: meta.clone(),
                });
            }
            Stmt::Expr { id, expr, meta } => {
                let e = extract_and_record(expr, eg, best, scope, rewrites, cost_before, cost_after);
                out.push(Stmt::Expr {
                    id: *id,
                    expr: e,
                    meta: meta.clone(),
                });
            }
        }
    }
    out
}

fn extract_and_record(
    orig: &Expr,
    eg: &mut EGraph,
    best: &BTreeMap<EClassId, (u64, ENode)>,
    scope: &str,
    rewrites: &mut Vec<EGraphRewriteWitness>,
    cost_before: &mut u64,
    cost_after: &mut u64,
) -> Expr {
    let orig_cost = expr_gas_cost(orig);
    let cid = eg.add_expr(orig);
    let root = eg.find(cid);
    let (extracted, ext_cost) = eg.extract_expr(root, best, orig);

    let (chosen, chosen_cost) = if ext_cost < orig_cost {
        (extracted, ext_cost)
    } else {
        (orig.clone(), orig_cost)
    };

    *cost_before += orig_cost;
    *cost_after += chosen_cost;

    if chosen != *orig {
        let class_size = eg.classes.get(&root).map(|c| c.nodes.len()).unwrap_or(1);
        rewrites.push(EGraphRewriteWitness {
            scope: scope.to_string(),
            eclass_id: root,
            before_expr: format_expr_compact(orig),
            after_expr: format_expr_compact(&chosen),
            cost_before: orig_cost,
            cost_after: chosen_cost,
            class_size,
        });
    }
    chosen
}

fn render_egraph_mermaid(
    eg: &EGraph,
    best: &BTreeMap<EClassId, (u64, ENode)>,
    rewrites: &[EGraphRewriteWitness],
) -> String {
    let mut lines = vec!["flowchart TD".to_string()];
    let mut shown_classes: BTreeSet<EClassId> = rewrites.iter().map(|r| r.eclass_id).collect();
    if shown_classes.is_empty() {
        for (&cid, cls) in &eg.classes {
            if cls.nodes.len() > 1 {
                shown_classes.insert(cid);
            }
            if shown_classes.len() >= 6 {
                break;
            }
        }
    }

    for &cid in shown_classes.iter().take(8) {
        if let Some(cls) = eg.classes.get(&cid) {
            let best_cost = best.get(&cid).map(|(c, _)| *c).unwrap_or(1);
            lines.push(format!(
                "  subgraph EC{}[\"E-Class #{} ({} eq forms · min cost {})\" ]",
                cid,
                cid,
                cls.nodes.len(),
                best_cost
            ));
            for (idx, n) in cls.nodes.iter().take(4).enumerate() {
                let lbl = format!("{:?}", n).replace('"', "'");
                lines.push(format!("    N{}_{}[\"{}\"]", cid, idx, lbl));
            }
            lines.push("  end".to_string());
        }
    }
    lines.join("\n")
}

/// Run Futamura-Projection Partial Evaluation, Interprocedural Constant/Enum Function Specialization,
/// Static Branch Elimination & E-Graph Superoptimization across `hub`.
pub fn partial_eval_module(hub: &HubModule) -> PartialEvalReport {
    let start = Instant::now();
    let nodes_before = hub.node_count();
    let ev_before = eval_module_default(hub);
    let comp_before = analyze_complexity(hub);
    let gas_before = comp_before.module_gas.total_gas;

    let mut fns_map: BTreeMap<String, FnDecl> = BTreeMap::new();
    for item in &hub.items {
        if let Item::Function(f) = item {
            fns_map.insert(f.name.clone(), f.clone());
        }
    }

    let mut next_id = hub.next_id.max(10_000);
    let mut alloc_id = || {
        let id = next_id;
        next_id += 1;
        id
    };

    let mut specializations: Vec<SpecializationSite> = Vec::new();
    let mut synthesized_fns: BTreeMap<String, FnDecl> = BTreeMap::new();
    let mut static_branches_folded = 0usize;
    let mut loops_unrolled = 0usize;

    let mut new_items: Vec<Item> = Vec::new();
    for item in &hub.items {
        match item {
            Item::Function(f) => {
                let mut env: BTreeMap<String, Expr> = BTreeMap::new();
                let new_body = peval_stmts(
                    &f.name,
                    &f.body,
                    &mut env,
                    &fns_map,
                    &mut synthesized_fns,
                    &mut specializations,
                    &mut static_branches_folded,
                    &mut loops_unrolled,
                    &mut alloc_id,
                );
                let mut f2 = f.clone();
                f2.body = new_body;
                new_items.push(Item::Function(f2));
            }
            other => new_items.push(other.clone()),
        }
    }

    // Insert any specialized residual functions right before `main` (or at the end of functions)
    let residual_functions_synthesized = synthesized_fns.len();
    if !synthesized_fns.is_empty() {
        let mut with_specs = Vec::with_capacity(new_items.len() + synthesized_fns.len());
        let mut inserted = false;
        for item in new_items {
            if !inserted && matches!(&item, Item::Function(f) if f.name == "main") {
                for sf in synthesized_fns.values() {
                    with_specs.push(Item::Function(sf.clone()));
                }
                inserted = true;
            }
            with_specs.push(item);
        }
        if !inserted {
            for sf in synthesized_fns.values() {
                with_specs.push(Item::Function(sf.clone()));
            }
        }
        new_items = with_specs;
    }

    let intermediate_hub = HubModule {
        items: new_items,
        next_id,
    };

    // Chain into E-Graph Equality Saturation Superoptimizer on the partially evaluated module!
    let eg_rep = superoptimize_egraph(&intermediate_hub);
    let residual_hub = eg_rep.optimized_hub;
    let static_branches_total = static_branches_folded + eg_rep.dead_branches_pruned;

    let ev_after = eval_module_default(&residual_hub);
    let tests_after = eval_tests_default(&residual_hub);
    let comp_after = analyze_complexity(&residual_hub);
    let gas_after = comp_after.module_gas.total_gas;
    let nodes_after = residual_hub.node_count();

    let tests_passed = tests_after.iter().filter(|t| t.passed).count();
    let tests_total = tests_after.len();
    let translation_validated = ev_before.ok == ev_after.ok
        && ev_before.stdout == ev_after.stdout
        && tests_passed == tests_total;

    let mut views_by_spoke = BTreeMap::new();
    for spoke in SpokeId::ALL {
        views_by_spoke.insert(spoke.as_str().to_string(), lens_for(spoke).get(&residual_hub));
    }

    PartialEvalReport {
        specialized_calls: specializations.len(),
        residual_functions_synthesized,
        static_branches_folded: static_branches_total,
        loops_unrolled,
        egraph_rewrites: eg_rep.expressions_optimized,
        nodes_before,
        nodes_after,
        vm_steps_before: ev_before.steps,
        vm_steps_after: ev_after.steps,
        gas_before,
        gas_after,
        translation_validated,
        stdout_before: ev_before.stdout.trim().to_string(),
        stdout_after: ev_after.stdout.trim().to_string(),
        tests_passed,
        tests_total,
        specializations,
        views_by_spoke,
        residual_hub,
        elapsed_ms: start.elapsed().as_millis(),
    }
}

fn is_static_literal(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Int(_)
            | Expr::Float(_)
            | Expr::Bool(_)
            | Expr::Str(_)
            | Expr::EnumVariant { .. }
    )
}

fn collect_modified_vars(stmts: &[Stmt], out: &mut BTreeSet<String>) {
    for s in stmts {
        match s {
            Stmt::Let { name, .. } => {
                out.insert(name.clone());
            }
            Stmt::Assign { target, .. } => {
                out.insert(target.root_var().to_string());
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_modified_vars(then_body, out);
                collect_modified_vars(else_body, out);
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    collect_modified_vars(&a.body, out);
                }
            }
            Stmt::While { body, .. } => {
                collect_modified_vars(body, out);
            }
            Stmt::ForEach { var, body, .. } | Stmt::ForRange { var, body, .. } => {
                out.insert(var.clone());
                collect_modified_vars(body, out);
            }
            Stmt::Expr {
                expr: Expr::Intrinsic(intr),
                ..
            } => {
                if let Intrinsic::Push {
                    list: Expr::Var(v), ..
                } = intr.as_ref()
                {
                    out.insert(v.clone());
                }
            }
            _ => {}
        }
    }
}

fn contains_break_continue_or_return(stmts: &[Stmt]) -> bool {
    for s in stmts {
        match s {
            Stmt::Break { .. } | Stmt::Continue { .. } | Stmt::Return { .. } => return true,
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                if contains_break_continue_or_return(then_body)
                    || contains_break_continue_or_return(else_body)
                {
                    return true;
                }
            }
            Stmt::Match { arms, .. } => {
                if arms
                    .iter()
                    .any(|a| contains_break_continue_or_return(&a.body))
                {
                    return true;
                }
            }
            Stmt::While { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::ForRange { body, .. }
                if contains_break_continue_or_return(body) => {
                    return true;
                }
            _ => {}
        }
    }
    false
}

#[allow(clippy::too_many_arguments)]
fn peval_stmts(
    caller_name: &str,
    stmts: &[Stmt],
    env: &mut BTreeMap<String, Expr>,
    fns_map: &BTreeMap<String, FnDecl>,
    synthesized_fns: &mut BTreeMap<String, FnDecl>,
    specializations: &mut Vec<SpecializationSite>,
    static_branches_folded: &mut usize,
    loops_unrolled: &mut usize,
    alloc_id: &mut impl FnMut() -> u64,
) -> Vec<Stmt> {
    let mut out = Vec::new();
    for stmt in stmts {
        if matches!(out.last(), Some(Stmt::Return { .. })) {
            break;
        }
        match stmt {
            Stmt::Comment { .. } | Stmt::Break { .. } | Stmt::Continue { .. } => {
                out.push(stmt.clone());
            }
            Stmt::Let {
                id,
                name,
                mutable,
                ty,
                value,
                meta,
            } => {
                let v = peval_expr(
                    caller_name,
                    value,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                if !*mutable && is_static_literal(&v) {
                    env.insert(name.clone(), v.clone());
                } else {
                    env.remove(name);
                }
                out.push(Stmt::Let {
                    id: *id,
                    name: name.clone(),
                    mutable: *mutable,
                    ty: ty.clone(),
                    value: v,
                    meta: meta.clone(),
                });
            }
            Stmt::Assign {
                id,
                target,
                op,
                value,
                meta,
            } => {
                let v = peval_expr(
                    caller_name,
                    value,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                env.remove(target.root_var());
                out.push(Stmt::Assign {
                    id: *id,
                    target: target.clone(),
                    op: *op,
                    value: v,
                    meta: meta.clone(),
                });
            }
            Stmt::If {
                id,
                cond,
                then_body,
                else_body,
                meta,
            } => {
                let c = peval_expr(
                    caller_name,
                    cond,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                match &c {
                    Expr::Bool(true) => {
                        *static_branches_folded += 1;
                        let tb = peval_stmts(
                            caller_name,
                            then_body,
                            env,
                            fns_map,
                            synthesized_fns,
                            specializations,
                            static_branches_folded,
                            loops_unrolled,
                            alloc_id,
                        );
                        out.extend(tb);
                    }
                    Expr::Bool(false) => {
                        *static_branches_folded += 1;
                        let eb = peval_stmts(
                            caller_name,
                            else_body,
                            env,
                            fns_map,
                            synthesized_fns,
                            specializations,
                            static_branches_folded,
                            loops_unrolled,
                            alloc_id,
                        );
                        out.extend(eb);
                    }
                    _ => {
                        let mut mod_vars = BTreeSet::new();
                        collect_modified_vars(then_body, &mut mod_vars);
                        collect_modified_vars(else_body, &mut mod_vars);
                        let mut then_env = env.clone();
                        let mut else_env = env.clone();
                        let tb = peval_stmts(
                            caller_name,
                            then_body,
                            &mut then_env,
                            fns_map,
                            synthesized_fns,
                            specializations,
                            static_branches_folded,
                            loops_unrolled,
                            alloc_id,
                        );
                        let eb = peval_stmts(
                            caller_name,
                            else_body,
                            &mut else_env,
                            fns_map,
                            synthesized_fns,
                            specializations,
                            static_branches_folded,
                            loops_unrolled,
                            alloc_id,
                        );
                        for mv in mod_vars {
                            env.remove(&mv);
                        }
                        out.push(Stmt::If {
                            id: *id,
                            cond: c,
                            then_body: tb,
                            else_body: eb,
                            meta: meta.clone(),
                        });
                    }
                }
            }
            Stmt::Match {
                id,
                expr,
                arms,
                meta,
            } => {
                let e = peval_expr(
                    caller_name,
                    expr,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                if let Some(matched_body) = try_match_static_arm(&e, arms) {
                    *static_branches_folded += 1;
                    let mb = peval_stmts(
                        caller_name,
                        matched_body,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    );
                    out.extend(mb);
                } else {
                    let mut mod_vars = BTreeSet::new();
                    for a in arms {
                        collect_modified_vars(&a.body, &mut mod_vars);
                    }
                    let mut new_arms = Vec::with_capacity(arms.len());
                    for a in arms {
                        let mut arm_env = env.clone();
                        let ab = peval_stmts(
                            caller_name,
                            &a.body,
                            &mut arm_env,
                            fns_map,
                            synthesized_fns,
                            specializations,
                            static_branches_folded,
                            loops_unrolled,
                            alloc_id,
                        );
                        new_arms.push(crate::hub::MatchArm {
                            pat: a.pat.clone(),
                            body: ab,
                        });
                    }
                    for mv in mod_vars {
                        env.remove(&mv);
                    }
                    out.push(Stmt::Match {
                        id: *id,
                        expr: e,
                        arms: new_arms,
                        meta: meta.clone(),
                    });
                }
            }
            Stmt::ForRange {
                id,
                var,
                start,
                end,
                body,
                meta,
            } => {
                let s = peval_expr(
                    caller_name,
                    start,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                let e = peval_expr(
                    caller_name,
                    end,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                if let (Expr::Int(lo), Expr::Int(hi)) = (&s, &e) {
                    let has_inner_let = body.iter().any(|st| matches!(st, Stmt::Let { .. }));
                    if let Some(trip) = hi.checked_sub(*lo) {
                        if (0..=4).contains(&trip)
                            && !has_inner_let
                            && !contains_break_continue_or_return(body)
                        {
                            *loops_unrolled += 1;
                            let prev_var = env.get(var).cloned();
                            let mut mod_vars = BTreeSet::new();
                            collect_modified_vars(body, &mut mod_vars);
                            for mv in &mod_vars {
                                env.remove(mv);
                            }
                            for idx in *lo..*hi {
                                env.insert(var.clone(), Expr::Int(idx));
                                let iter_stmts = peval_stmts(
                                    caller_name,
                                    body,
                                    env,
                                    fns_map,
                                    synthesized_fns,
                                    specializations,
                                    static_branches_folded,
                                    loops_unrolled,
                                    alloc_id,
                                );
                                out.extend(iter_stmts);
                            }
                            if let Some(pv) = prev_var {
                                env.insert(var.clone(), pv);
                            } else {
                                env.remove(var);
                            }
                            continue;
                        }
                    }
                }
                let mut mod_vars = BTreeSet::new();
                mod_vars.insert(var.clone());
                collect_modified_vars(body, &mut mod_vars);
                for mv in &mod_vars {
                    env.remove(mv);
                }
                let mut loop_env = env.clone();
                let b = peval_stmts(
                    caller_name,
                    body,
                    &mut loop_env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                out.push(Stmt::ForRange {
                    id: *id,
                    var: var.clone(),
                    start: s,
                    end: e,
                    body: b,
                    meta: meta.clone(),
                });
            }
            Stmt::While {
                id,
                cond,
                body,
                meta,
            } => {
                let mut mod_vars = BTreeSet::new();
                collect_modified_vars(body, &mut mod_vars);
                for mv in &mod_vars {
                    env.remove(mv);
                }
                let c = peval_expr(
                    caller_name,
                    cond,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                let mut loop_env = env.clone();
                let b = peval_stmts(
                    caller_name,
                    body,
                    &mut loop_env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                out.push(Stmt::While {
                    id: *id,
                    cond: c,
                    body: b,
                    meta: meta.clone(),
                });
            }
            Stmt::ForEach {
                id,
                var,
                iter,
                body,
                meta,
            } => {
                let it = peval_expr(
                    caller_name,
                    iter,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                let mut mod_vars = BTreeSet::new();
                mod_vars.insert(var.clone());
                collect_modified_vars(body, &mut mod_vars);
                for mv in &mod_vars {
                    env.remove(mv);
                }
                let mut loop_env = env.clone();
                let b = peval_stmts(
                    caller_name,
                    body,
                    &mut loop_env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                out.push(Stmt::ForEach {
                    id: *id,
                    var: var.clone(),
                    iter: it,
                    body: b,
                    meta: meta.clone(),
                });
            }
            Stmt::Return { id, value, meta } => {
                let v = value.as_ref().map(|e| {
                    peval_expr(
                        caller_name,
                        e,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    )
                });
                out.push(Stmt::Return {
                    id: *id,
                    value: v,
                    meta: meta.clone(),
                });
            }
            Stmt::Assert { id, cond, meta } => {
                let c = peval_expr(
                    caller_name,
                    cond,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                out.push(Stmt::Assert {
                    id: *id,
                    cond: c,
                    meta: meta.clone(),
                });
            }
            Stmt::AssertEq {
                id,
                left,
                right,
                meta,
            } => {
                let l = peval_expr(
                    caller_name,
                    left,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                let r = peval_expr(
                    caller_name,
                    right,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                out.push(Stmt::AssertEq {
                    id: *id,
                    left: l,
                    right: r,
                    meta: meta.clone(),
                });
            }
            Stmt::Expr { id, expr, meta } => {
                let e = peval_expr(
                    caller_name,
                    expr,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                );
                out.push(Stmt::Expr {
                    id: *id,
                    expr: e,
                    meta: meta.clone(),
                });
            }
        }
    }
    out
}

fn try_match_static_arm<'a>(
    scrutinee: &Expr,
    arms: &'a [crate::hub::MatchArm],
) -> Option<&'a [Stmt]> {
    for arm in arms {
        match (&arm.pat, scrutinee) {
            (MatchPat::Wildcard, _) if is_static_literal(scrutinee) => return Some(&arm.body),
            (
                MatchPat::EnumVariant {
                    enum_name: e1,
                    variant: v1,
                },
                Expr::EnumVariant {
                    enum_name: e2,
                    variant: v2,
                },
            ) if e1 == e2 && v1 == v2 => return Some(&arm.body),
            (MatchPat::Int(a), Expr::Int(b)) if a == b => return Some(&arm.body),
            (MatchPat::Str(a), Expr::Str(b)) if a == b => return Some(&arm.body),
            _ => {}
        }
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn peval_expr(
    caller_name: &str,
    expr: &Expr,
    env: &BTreeMap<String, Expr>,
    fns_map: &BTreeMap<String, FnDecl>,
    synthesized_fns: &mut BTreeMap<String, FnDecl>,
    specializations: &mut Vec<SpecializationSite>,
    static_branches_folded: &mut usize,
    loops_unrolled: &mut usize,
    alloc_id: &mut impl FnMut() -> u64,
) -> Expr {
    match expr {
        Expr::Var(v) => env.get(v).cloned().unwrap_or_else(|| expr.clone()),
        Expr::List(items) => Expr::List(
            items
                .iter()
                .map(|i| {
                    peval_expr(
                        caller_name,
                        i,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    )
                })
                .collect(),
        ),
        Expr::StructInit { name, fields } => Expr::StructInit {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(k, v)| {
                    (
                        k.clone(),
                        peval_expr(
                            caller_name,
                            v,
                            env,
                            fns_map,
                            synthesized_fns,
                            specializations,
                            static_branches_folded,
                            loops_unrolled,
                            alloc_id,
                        ),
                    )
                })
                .collect(),
        },
        Expr::FieldAccess { base, field } => {
            let b = peval_expr(
                caller_name,
                base,
                env,
                fns_map,
                synthesized_fns,
                specializations,
                static_branches_folded,
                loops_unrolled,
                alloc_id,
            );
            if let Expr::StructInit { fields, .. } = &b {
                if let Some((_, val)) = fields.iter().find(|(k, _)| k == field) {
                    return val.clone();
                }
            }
            Expr::FieldAccess {
                base: Box::new(b),
                field: field.clone(),
            }
        }
        Expr::Index { base, index } => Expr::Index {
            base: Box::new(peval_expr(
                caller_name,
                base,
                env,
                fns_map,
                synthesized_fns,
                specializations,
                static_branches_folded,
                loops_unrolled,
                alloc_id,
            )),
            index: Box::new(peval_expr(
                caller_name,
                index,
                env,
                fns_map,
                synthesized_fns,
                specializations,
                static_branches_folded,
                loops_unrolled,
                alloc_id,
            )),
        },
        Expr::Unary { op, expr: inner } => Expr::Unary {
            op: *op,
            expr: Box::new(peval_expr(
                caller_name,
                inner,
                env,
                fns_map,
                synthesized_fns,
                specializations,
                static_branches_folded,
                loops_unrolled,
                alloc_id,
            )),
        },
        Expr::Binary { op, left, right } => Expr::Binary {
            op: *op,
            left: Box::new(peval_expr(
                caller_name,
                left,
                env,
                fns_map,
                synthesized_fns,
                specializations,
                static_branches_folded,
                loops_unrolled,
                alloc_id,
            )),
            right: Box::new(peval_expr(
                caller_name,
                right,
                env,
                fns_map,
                synthesized_fns,
                specializations,
                static_branches_folded,
                loops_unrolled,
                alloc_id,
            )),
        },
        Expr::Intrinsic(intr) => {
            let mapped = match intr.as_ref() {
                Intrinsic::Len(a) => Intrinsic::Len(peval_expr(
                    caller_name,
                    a,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                )),
                Intrinsic::Min(a, b) => Intrinsic::Min(
                    peval_expr(
                        caller_name,
                        a,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    ),
                    peval_expr(
                        caller_name,
                        b,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    ),
                ),
                Intrinsic::Max(a, b) => Intrinsic::Max(
                    peval_expr(
                        caller_name,
                        a,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    ),
                    peval_expr(
                        caller_name,
                        b,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    ),
                ),
                Intrinsic::Abs(a) => Intrinsic::Abs(peval_expr(
                    caller_name,
                    a,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                )),
                Intrinsic::Push { list, value } => Intrinsic::Push {
                    list: peval_expr(
                        caller_name,
                        list,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    ),
                    value: peval_expr(
                        caller_name,
                        value,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    ),
                },
                Intrinsic::Print(args) => Intrinsic::Print(
                    args.iter()
                        .map(|a| {
                            peval_expr(
                                caller_name,
                                a,
                                env,
                                fns_map,
                                synthesized_fns,
                                specializations,
                                static_branches_folded,
                                loops_unrolled,
                                alloc_id,
                            )
                        })
                        .collect(),
                ),
                Intrinsic::Contains { haystack, needle } => Intrinsic::Contains {
                    haystack: peval_expr(
                        caller_name,
                        haystack,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    ),
                    needle: peval_expr(
                        caller_name,
                        needle,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    ),
                },
                Intrinsic::Upper(a) => Intrinsic::Upper(peval_expr(
                    caller_name,
                    a,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                )),
                Intrinsic::Lower(a) => Intrinsic::Lower(peval_expr(
                    caller_name,
                    a,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                )),
                Intrinsic::ToStr(a) => Intrinsic::ToStr(peval_expr(
                    caller_name,
                    a,
                    env,
                    fns_map,
                    synthesized_fns,
                    specializations,
                    static_branches_folded,
                    loops_unrolled,
                    alloc_id,
                )),
            };
            Expr::intrinsic(mapped)
        }
        Expr::Call { func, args } => {
            let eval_args: Vec<Expr> = args
                .iter()
                .map(|a| {
                    peval_expr(
                        caller_name,
                        a,
                        env,
                        fns_map,
                        synthesized_fns,
                        specializations,
                        static_branches_folded,
                        loops_unrolled,
                        alloc_id,
                    )
                })
                .collect();

            // Futamura specialization on non-recursive functions with static arguments
            if func != caller_name {
                if let Some(callee) = fns_map.get(func) {
                    if callee.params.len() == eval_args.len() && !callee.params.is_empty() {
                        // Case A: All arguments are static literals and callee reduces to a single Return expression
                        if eval_args.iter().all(is_static_literal) {
                            let mut call_env = BTreeMap::new();
                            for (p, a) in callee.params.iter().zip(eval_args.iter()) {
                                call_env.insert(p.name.clone(), a.clone());
                            }
                            let reduced_body = peval_stmts(
                                &callee.name,
                                &callee.body,
                                &mut call_env,
                                fns_map,
                                synthesized_fns,
                                specializations,
                                static_branches_folded,
                                loops_unrolled,
                                alloc_id,
                            );
                            if let [Stmt::Return {
                                value: Some(ret_expr),
                                ..
                            }] = reduced_body.as_slice()
                            {
                                let bindings_str = callee
                                    .params
                                    .iter()
                                    .zip(eval_args.iter())
                                    .map(|(p, a)| format!("{}={}", p.name, format_expr_compact(a)))
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                specializations.push(SpecializationSite {
                                    caller: caller_name.to_string(),
                                    callee: func.clone(),
                                    specialized_name: format!("inline({})", func),
                                    static_bindings: bindings_str,
                                    summary: format!(
                                        "{}({}) => {}",
                                        func,
                                        eval_args
                                            .iter()
                                            .map(format_expr_compact)
                                            .collect::<Vec<_>>()
                                            .join(", "),
                                        format_expr_compact(ret_expr)
                                    ),
                                });
                                return ret_expr.clone();
                            }
                        }

                        // Case B: Mixed static + dynamic arguments (e.g., static EnumVariant or Int policy/cap)
                        let has_static = eval_args.iter().any(is_static_literal);
                        let has_dynamic = eval_args.iter().any(|a| !is_static_literal(a));
                        if has_static && has_dynamic && caller_name == "main" {
                            let mut suffix_parts = Vec::new();
                            let mut residual_params = Vec::new();
                            let mut residual_args = Vec::new();
                            let mut spec_env = BTreeMap::new();
                            let mut binding_notes = Vec::new();

                            for (p, a) in callee.params.iter().zip(eval_args.iter()) {
                                if is_static_literal(a) {
                                    let tag = match a {
                                        Expr::Int(v) if *v >= 0 => format!("i{}", v),
                                        Expr::Int(v) => format!("in{}", v.unsigned_abs()),
                                        Expr::EnumVariant { variant, .. } => {
                                            variant.to_lowercase()
                                        }
                                        Expr::Bool(b) => format!("b{}", b),
                                        _ => "const".to_string(),
                                    };
                                    suffix_parts.push(tag);
                                    spec_env.insert(p.name.clone(), a.clone());
                                    binding_notes
                                        .push(format!("{}={}", p.name, format_expr_compact(a)));
                                } else {
                                    residual_params.push(p.clone());
                                    residual_args.push(a.clone());
                                }
                            }

                            let spec_name = format!("{}_spec_{}", callee.name, suffix_parts.join("_"));
                            if !synthesized_fns.contains_key(&spec_name)
                                && !fns_map.contains_key(&spec_name)
                            {
                                let spec_body = peval_stmts(
                                    &spec_name,
                                    &callee.body,
                                    &mut spec_env,
                                    fns_map,
                                    synthesized_fns,
                                    specializations,
                                    static_branches_folded,
                                    loops_unrolled,
                                    alloc_id,
                                );
                                let spec_fn = FnDecl {
                                    id: alloc_id(),
                                    name: spec_name.clone(),
                                    params: residual_params,
                                    ret_ty: callee.ret_ty.clone(),
                                    body: spec_body,
                                    comments: vec![format!(
                                        "Futamura-specialized residual of {}() for [{}]",
                                        callee.name,
                                        binding_notes.join(", ")
                                    )],
                                    meta: callee.meta.clone(),
                                };
                                synthesized_fns.insert(spec_name.clone(), spec_fn);
                            }

                            specializations.push(SpecializationSite {
                                caller: caller_name.to_string(),
                                callee: func.clone(),
                                specialized_name: spec_name.clone(),
                                static_bindings: binding_notes.join(", "),
                                summary: format!(
                                    "{}(...) -> {}({})",
                                    func,
                                    spec_name,
                                    residual_args
                                        .iter()
                                        .map(format_expr_compact)
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                ),
                            });

                            return Expr::Call {
                                func: spec_name,
                                args: residual_args,
                            };
                        }
                    }
                }
            }

            Expr::Call {
                func: func.clone(),
                args: eval_args,
            }
        }
        other => other.clone(),
    }
}

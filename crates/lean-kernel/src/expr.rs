use crate::level::Level;
use crate::name::Name;
use lean_eterned::BaseCoword;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    BVar(u32),
    FVar(Name),
    MVar(Name),
    Sort(Level),
    Const(Name, Vec<Level>),
    App(Box<Expr>, Box<Expr>),
    Lam(Name, Box<Expr>, Box<Expr>, BinderInfo),
    Forall(Name, Box<Expr>, Box<Expr>, BinderInfo),
    Let(Name, Box<Expr>, Box<Expr>, Box<Expr>),
    Lit(Literal),
    MData(MData, Box<Expr>),
    Proj(Name, u32, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Nat(u64),
    String(BaseCoword),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MData {
    pub name: Name,
    pub data: Vec<Expr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

impl Expr {
    pub fn bvar(idx: u32) -> Self {
        Expr { kind: ExprKind::BVar(idx) }
    }

    pub fn fvar(name: Name) -> Self {
        Expr { kind: ExprKind::FVar(name) }
    }

    pub fn mvar(name: Name) -> Self {
        Expr { kind: ExprKind::MVar(name) }
    }

    pub fn sort(level: Level) -> Self {
        Expr { kind: ExprKind::Sort(level) }
    }

    pub fn const_expr(name: Name, levels: Vec<Level>) -> Self {
        Expr { kind: ExprKind::Const(name, levels) }
    }

    pub fn app(f: Expr, arg: Expr) -> Self {
        Expr { kind: ExprKind::App(Box::new(f), Box::new(arg)) }
    }

    pub fn lam(name: Name, ty: Expr, body: Expr, binder_info: BinderInfo) -> Self {
        Expr {
            kind: ExprKind::Lam(name, Box::new(ty), Box::new(body), binder_info),
        }
    }

    pub fn forall(name: Name, ty: Expr, body: Expr, binder_info: BinderInfo) -> Self {
        Expr {
            kind: ExprKind::Forall(name, Box::new(ty), Box::new(body), binder_info),
        }
    }

    pub fn let_expr(name: Name, ty: Expr, value: Expr, body: Expr) -> Self {
        Expr {
            kind: ExprKind::Let(name, Box::new(ty), Box::new(value), Box::new(body)),
        }
    }

    pub fn nat(n: u64) -> Self {
        Expr { kind: ExprKind::Lit(Literal::Nat(n)) }
    }

    pub fn string(s: impl Into<BaseCoword>) -> Self {
        Expr { kind: ExprKind::Lit(Literal::String(s.into())) }
    }

    pub fn proj(struct_name: Name, idx: u32, expr: Expr) -> Self {
        Expr { kind: ExprKind::Proj(struct_name, idx, Box::new(expr)) }
    }

    pub fn is_bvar(&self) -> bool {
        matches!(self.kind, ExprKind::BVar(_))
    }

    pub fn is_fvar(&self) -> bool {
        matches!(self.kind, ExprKind::FVar(_))
    }

    pub fn is_mvar(&self) -> bool {
        matches!(self.kind, ExprKind::MVar(_))
    }

    pub fn is_sort(&self) -> bool {
        matches!(self.kind, ExprKind::Sort(_))
    }

    pub fn is_const(&self) -> bool {
        matches!(self.kind, ExprKind::Const(_, _))
    }

    pub fn is_app(&self) -> bool {
        matches!(self.kind, ExprKind::App(_, _))
    }

    pub fn is_lambda(&self) -> bool {
        matches!(self.kind, ExprKind::Lam(_, _, _, _))
    }

    pub fn is_forall(&self) -> bool {
        matches!(self.kind, ExprKind::Forall(_, _, _, _))
    }

    pub fn is_let(&self) -> bool {
        matches!(self.kind, ExprKind::Let(_, _, _, _))
    }

    pub fn loose_bvar_range(&self) -> u32 {
        self.loose_bvar_range_aux(0)
    }

    fn loose_bvar_range_aux(&self, offset: u32) -> u32 {
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx >= offset {
                    idx - offset + 1
                } else {
                    0
                }
            }
            ExprKind::App(f, arg) => {
                f.loose_bvar_range_aux(offset).max(arg.loose_bvar_range_aux(offset))
            }
            ExprKind::Lam(_, ty, body, _) | ExprKind::Forall(_, ty, body, _) => {
                ty.loose_bvar_range_aux(offset).max(body.loose_bvar_range_aux(offset + 1))
            }
            ExprKind::Let(_, ty, value, body) => {
                ty.loose_bvar_range_aux(offset)
                    .max(value.loose_bvar_range_aux(offset))
                    .max(body.loose_bvar_range_aux(offset + 1))
            }
            ExprKind::MData(_, expr) | ExprKind::Proj(_, _, expr) => {
                expr.loose_bvar_range_aux(offset)
            }
            _ => 0,
        }
    }

    pub fn has_loose_bvars(&self) -> bool {
        self.loose_bvar_range() > 0
    }
}

impl fmt::Display for BinderInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinderInfo::Default => write!(f, ""),
            BinderInfo::Implicit => write!(f, "{{}}"),
            BinderInfo::StrictImplicit => write!(f, "⦃⦄"),
            BinderInfo::InstImplicit => write!(f, "[]"),
        }
    }
}
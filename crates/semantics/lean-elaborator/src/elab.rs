//! Main elaborator implementation
//!
//! The elaborator converts surface syntax into kernel expressions,
//! performing type inference and filling in implicit arguments.

use lean_kernel::{
    expr::{BinderInfo, ExprKind},
    Expr, Level, Name,
};
use lean_syn_expr::{Syntax, SyntaxKind};

use crate::{
    context::{LevelContext, LocalContext},
    error::ElabError,
    metavar::MetavarContext,
};

/// Elaboration state
pub struct ElabState {
    /// Local variable context
    pub lctx: LocalContext,
    /// Metavariable context
    pub mctx: MetavarContext,
    /// Universe level context
    pub level_ctx: LevelContext,
}

impl ElabState {
    pub fn new() -> Self {
        Self {
            lctx: LocalContext::new(),
            mctx: MetavarContext::new(),
            level_ctx: LevelContext::new(),
        }
    }
}

impl Default for ElabState {
    fn default() -> Self {
        Self::new()
    }
}

/// Main elaborator
pub struct Elaborator {
    state: ElabState,
}

impl Elaborator {
    pub fn new() -> Self {
        Self {
            state: ElabState::new(),
        }
    }

    /// Elaborate a syntax tree into a kernel expression
    pub fn elaborate(&mut self, syntax: &Syntax) -> Result<Expr, ElabError> {
        match syntax {
            Syntax::Missing => Err(ElabError::MissingSyntax),
            Syntax::Atom(atom) => self.elab_atom(atom),
            Syntax::Node(node) => self.elab_node(node),
        }
    }

    /// Elaborate an atomic syntax element
    fn elab_atom(&mut self, atom: &lean_syn_expr::SyntaxAtom) -> Result<Expr, ElabError> {
        let s = atom.value.as_str();

        // Try to parse as a number literal
        if let Ok(n) = s.parse::<u64>() {
            return Ok(Expr::nat(n));
        }

        // Try to parse as a string literal
        if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
            let content = &s[1..s.len() - 1];
            return Ok(Expr::string(content));
        }

        // Otherwise treat as an identifier
        let name = Name::mk_simple(s);

        // Check if it's a local variable
        if let Some(fvar_id) = self.state.lctx.find_by_user_name(&name) {
            return Ok(Expr::fvar(fvar_id.clone()));
        }

        // Otherwise treat as a constant (will need to be resolved later)
        Ok(Expr::const_expr(name, vec![]))
    }

    /// Elaborate a syntax node
    fn elab_node(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<Expr, ElabError> {
        match node.kind {
            SyntaxKind::Lambda => self.elab_lambda(node),
            SyntaxKind::Forall => self.elab_forall(node),
            SyntaxKind::App => self.elab_app(node),
            SyntaxKind::Let => self.elab_let(node),
            SyntaxKind::NumLit => self.elab_num_lit(node),
            SyntaxKind::StringLit => self.elab_string_lit(node),
            SyntaxKind::Projection => self.elab_projection(node),
            SyntaxKind::Arrow => self.elab_arrow(node),
            _ => Err(ElabError::UnsupportedSyntax(node.kind)),
        }
    }

    /// Elaborate a lambda expression: λ x : A => b
    fn elab_lambda(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<Expr, ElabError> {
        if node.children.len() < 2 {
            return Err(ElabError::InvalidSyntax(
                "Lambda requires at least binder and body".into(),
            ));
        }

        // For now, handle simple case: λ x => body
        // TODO: Handle typed binders, multiple binders, etc.

        let binder = &node.children[0];
        let body_syntax = &node.children[node.children.len() - 1];

        // Create a metavariable for the binder type
        let binder_type = self.state.mctx.mk_metavar(
            Expr::sort(Level::zero()), // Type of the type is Sort 0 for now
            self.state.lctx.clone(),
        );

        // Get binder name
        let binder_name = match binder {
            Syntax::Atom(atom) => Name::mk_simple(atom.value.as_str()),
            _ => Name::anonymous(),
        };

        // Elaborate body in extended context
        let fvar_id = self
            .state
            .lctx
            .push_local_decl(binder_name.clone(), binder_type.clone());
        let body = self.elaborate(body_syntax)?;

        // Replace fvar with bvar in body before popping context
        // The fvar should become bvar(0) since it's the most recent binding
        let body = self.abstract_fvar_core(body, &fvar_id, 0, 0);

        self.state.lctx.pop();

        Ok(Expr::lam(
            binder_name,
            binder_type,
            body,
            BinderInfo::Default,
        ))
    }

    /// Elaborate a forall expression: ∀ x : A, B
    fn elab_forall(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<Expr, ElabError> {
        if node.children.len() < 2 {
            return Err(ElabError::InvalidSyntax(
                "Forall requires at least binder and body".into(),
            ));
        }

        // Similar to lambda for now
        let binder = &node.children[0];
        let body_syntax = &node.children[node.children.len() - 1];

        let binder_type = self
            .state
            .mctx
            .mk_metavar(Expr::sort(Level::zero()), self.state.lctx.clone());

        let binder_name = match binder {
            Syntax::Atom(atom) => Name::mk_simple(atom.value.as_str()),
            _ => Name::anonymous(),
        };

        let fvar_id = self
            .state
            .lctx
            .push_local_decl(binder_name.clone(), binder_type.clone());
        let body = self.elaborate(body_syntax)?;

        // Replace fvar with bvar before popping
        let body = self.abstract_fvar_core(body, &fvar_id, 0, 0);

        self.state.lctx.pop();

        Ok(Expr::forall(
            binder_name,
            binder_type,
            body,
            BinderInfo::Default,
        ))
    }

    /// Elaborate function application: f a
    fn elab_app(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<Expr, ElabError> {
        if node.children.is_empty() {
            return Err(ElabError::InvalidSyntax("Empty application".into()));
        }

        let mut result = self.elaborate(&node.children[0])?;

        for arg_syntax in &node.children[1..] {
            let arg = self.elaborate(arg_syntax)?;
            result = Expr::app(result, arg);
        }

        Ok(result)
    }

    /// Elaborate let expression: let x := v in b
    fn elab_let(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<Expr, ElabError> {
        if node.children.len() < 3 {
            return Err(ElabError::InvalidSyntax(
                "Let requires name, value, and body".into(),
            ));
        }

        let name_syntax = &node.children[0];
        let value_syntax = &node.children[1];
        let body_syntax = &node.children[2];

        let name = match name_syntax {
            Syntax::Atom(atom) => Name::mk_simple(atom.value.as_str()),
            _ => Name::anonymous(),
        };

        // Elaborate value
        let value = self.elaborate(value_syntax)?;

        // Infer type of value (for now, use metavariable)
        let value_type = self
            .state
            .mctx
            .mk_metavar(Expr::sort(Level::zero()), self.state.lctx.clone());

        // Elaborate body in extended context
        let fvar_id =
            self.state
                .lctx
                .push_local_def(name.clone(), Some(value_type.clone()), value.clone());
        let body = self.elaborate(body_syntax)?;

        // Replace fvar with bvar before popping
        let body = self.abstract_fvar_core(body, &fvar_id, 0, 0);

        self.state.lctx.pop();

        Ok(Expr::let_expr(name, value_type, value, body))
    }

    /// Elaborate number literal
    fn elab_num_lit(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<Expr, ElabError> {
        if let Some(Syntax::Atom(atom)) = node.children.first() {
            if let Ok(n) = atom.value.as_str().parse::<u64>() {
                return Ok(Expr::nat(n));
            }
        }
        Err(ElabError::InvalidSyntax("Invalid number literal".into()))
    }

    /// Elaborate string literal
    fn elab_string_lit(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<Expr, ElabError> {
        if let Some(Syntax::Atom(atom)) = node.children.first() {
            let s = atom.value.as_str();
            if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
                let content = &s[1..s.len() - 1];
                return Ok(Expr::string(content));
            }
        }
        Err(ElabError::InvalidSyntax("Invalid string literal".into()))
    }

    /// Elaborate projection: x.1 or x.field
    fn elab_projection(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<Expr, ElabError> {
        if node.children.len() != 2 {
            return Err(ElabError::InvalidSyntax(
                "Projection requires object and field".into(),
            ));
        }

        let obj = self.elaborate(&node.children[0])?;

        // Get field name/index
        match &node.children[1] {
            Syntax::Atom(atom) => {
                let field_str = atom.value.as_str();
                if let Ok(idx) = field_str.parse::<u32>() {
                    // Numeric projection
                    // TODO: We need to know the structure name
                    let struct_name = Name::mk_simple("_struct");
                    Ok(Expr::proj(struct_name, idx, obj))
                } else {
                    // Field name projection - need to resolve to index
                    // For now, use placeholder
                    let struct_name = Name::mk_simple("_struct");
                    Ok(Expr::proj(struct_name, 0, obj))
                }
            }
            _ => Err(ElabError::InvalidSyntax("Invalid projection field".into())),
        }
    }

    /// Elaborate arrow type: A → B
    fn elab_arrow(&mut self, node: &lean_syn_expr::SyntaxNode) -> Result<Expr, ElabError> {
        if node.children.len() != 3 {
            return Err(ElabError::InvalidSyntax(
                "Arrow requires domain and codomain".into(),
            ));
        }

        let domain = self.elaborate(&node.children[0])?;
        let codomain = self.elaborate(&node.children[2])?;

        // Arrow is sugar for forall with anonymous binder
        Ok(Expr::forall(
            Name::anonymous(),
            domain,
            codomain,
            BinderInfo::Default,
        ))
    }

    /// Abstract a free variable to a bound variable
    #[allow(dead_code)]
    fn abstract_fvar(&self, expr: Expr, fvar_id: &Name) -> Expr {
        // Calculate the De Bruijn index
        let bvar_idx = match self.state.lctx.fvar_to_bvar(fvar_id) {
            Some(idx) => idx,
            None => return expr, // fvar not in context, return unchanged
        };

        self.abstract_fvar_core(expr, fvar_id, bvar_idx, 0)
    }

    #[allow(clippy::only_used_in_recursion)]
    fn abstract_fvar_core(&self, expr: Expr, fvar_id: &Name, target_idx: u32, depth: u32) -> Expr {
        match &expr.kind {
            ExprKind::FVar(name) if name == fvar_id => {
                // Replace with bvar, adjusting for binding depth
                Expr::bvar(target_idx + depth)
            }
            ExprKind::App(f, a) => {
                let f_abs = self.abstract_fvar_core((**f).clone(), fvar_id, target_idx, depth);
                let a_abs = self.abstract_fvar_core((**a).clone(), fvar_id, target_idx, depth);
                Expr::app(f_abs, a_abs)
            }
            ExprKind::Lam(name, ty, body, info) => {
                let ty_abs = self.abstract_fvar_core((**ty).clone(), fvar_id, target_idx, depth);
                let body_abs =
                    self.abstract_fvar_core((**body).clone(), fvar_id, target_idx, depth + 1);
                Expr::lam(name.clone(), ty_abs, body_abs, *info)
            }
            ExprKind::Forall(name, ty, body, info) => {
                let ty_abs = self.abstract_fvar_core((**ty).clone(), fvar_id, target_idx, depth);
                let body_abs =
                    self.abstract_fvar_core((**body).clone(), fvar_id, target_idx, depth + 1);
                Expr::forall(name.clone(), ty_abs, body_abs, *info)
            }
            ExprKind::Let(name, ty, val, body) => {
                let ty_abs = self.abstract_fvar_core((**ty).clone(), fvar_id, target_idx, depth);
                let val_abs = self.abstract_fvar_core((**val).clone(), fvar_id, target_idx, depth);
                let body_abs =
                    self.abstract_fvar_core((**body).clone(), fvar_id, target_idx, depth + 1);
                Expr::let_expr(name.clone(), ty_abs, val_abs, body_abs)
            }
            _ => expr,
        }
    }
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use lean_parser::Parser;

    use super::*;

    #[test]
    fn test_elab_number() {
        let mut elab = Elaborator::new();
        let mut parser = Parser::new("42");
        let syntax = parser.term().unwrap();

        let expr = elab.elaborate(&syntax).unwrap();
        match &expr.kind {
            lean_kernel::expr::ExprKind::Lit(lean_kernel::expr::Literal::Nat(n)) => {
                assert_eq!(*n, 42);
            }
            _ => panic!("Expected number literal"),
        }
    }

    #[test]
    fn test_elab_lambda_simple() {
        let mut elab = Elaborator::new();
        let mut parser = Parser::new("λ x => x");
        let syntax = parser.term().unwrap();

        let expr = elab.elaborate(&syntax).unwrap();
        match &expr.kind {
            lean_kernel::expr::ExprKind::Lam(name, _ty, body, _) => {
                assert_eq!(name.to_string(), "x");
                // Body should be bvar(0)
                match &body.kind {
                    lean_kernel::expr::ExprKind::BVar(0) => {}
                    other => panic!("Expected bvar(0) in lambda body, got {other:?}"),
                }
            }
            _ => panic!("Expected lambda expression"),
        }
    }

    #[test]
    fn test_elab_app() {
        let mut elab = Elaborator::new();
        let mut parser = Parser::new("f x y");
        let syntax = parser.term().unwrap();

        let expr = elab.elaborate(&syntax).unwrap();
        // Should be App(App(f, x), y)
        match &expr.kind {
            lean_kernel::expr::ExprKind::App(f_x, y) => match &f_x.kind {
                lean_kernel::expr::ExprKind::App(f, x) => match (&f.kind, &x.kind, &y.kind) {
                    (
                        lean_kernel::expr::ExprKind::Const(f_name, _),
                        lean_kernel::expr::ExprKind::Const(x_name, _),
                        lean_kernel::expr::ExprKind::Const(y_name, _),
                    ) => {
                        assert_eq!(f_name.to_string(), "f");
                        assert_eq!(x_name.to_string(), "x");
                        assert_eq!(y_name.to_string(), "y");
                    }
                    _ => panic!("Expected constants"),
                },
                _ => panic!("Expected nested application"),
            },
            _ => panic!("Expected application"),
        }
    }
}

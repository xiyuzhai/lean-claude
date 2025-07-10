use lean_syn_expr::{Syntax, SyntaxKind, SyntaxNode};
use smallvec::smallvec;

use crate::{
    environment::MacroEnvironment,
    error::{ExpansionError, ExpansionResult},
    hygiene::HygieneContext,
    pattern::{substitute_template, PatternMatcher},
};

/// A macro parameter specification
#[derive(Debug, Clone)]
struct MacroParameter {
    name: eterned::BaseCoword,
    #[allow(dead_code)]
    category: eterned::BaseCoword,
}

/// Main macro expander
pub struct MacroExpander {
    env: MacroEnvironment,
    hygiene: HygieneContext,
}

impl MacroExpander {
    pub fn new(env: MacroEnvironment) -> Self {
        let mut expander = Self {
            env,
            hygiene: HygieneContext::new(),
        };
        expander.register_builtins();
        expander
    }

    /// Expand all macros in a syntax tree
    pub fn expand(&mut self, syntax: &Syntax) -> ExpansionResult<Syntax> {
        self.expand_with_context(syntax, &self.hygiene.clone())
    }

    fn expand_with_context(
        &mut self,
        syntax: &Syntax,
        ctx: &HygieneContext,
    ) -> ExpansionResult<Syntax> {
        // Check expansion depth
        let new_ctx = ctx
            .enter_expansion()
            .ok_or(ExpansionError::ExpansionLimitExceeded {
                limit: ctx.max_depth,
            })?;

        match syntax {
            Syntax::Node(node) => {
                // Check if this is a macro application
                if let Some(expanded) = self.try_expand_macro(node, &new_ctx)? {
                    // Recursively expand the result
                    self.expand_with_context(&expanded, &new_ctx)
                } else {
                    // Not a macro, recursively expand children
                    self.expand_node(node, &new_ctx)
                }
            }
            Syntax::Atom(atom) => {
                // Check if this atom is a parameterless macro
                if let Some(expanded) = self.try_expand_atom_macro(atom, &new_ctx)? {
                    // Recursively expand the result
                    self.expand_with_context(&expanded, &new_ctx)
                } else {
                    Ok(syntax.clone())
                }
            }
            // Missing is returned as-is
            _ => Ok(syntax.clone()),
        }
    }

    /// Try to expand an atom as a parameterless macro
    fn try_expand_atom_macro(
        &self,
        atom: &lean_syn_expr::SyntaxAtom,
        _ctx: &HygieneContext,
    ) -> ExpansionResult<Option<Syntax>> {
        let macro_name = atom.value.as_str();

        // Look up macro definitions
        let macros = match self.env.get_macros(macro_name) {
            Some(macros) => macros,
            None => return Ok(None),
        };

        // Try each macro definition in order
        for macro_def in macros {
            // Check if this macro accepts no parameters
            if matches!(&macro_def.pattern, Syntax::Missing) {
                // Match succeeded, substitute into template
                let bindings = im::HashMap::new();
                let expanded = substitute_template(&macro_def.template, &bindings)?;

                // If the template result is a SyntaxQuotation, unwrap it
                let final_expansion = match &expanded {
                    Syntax::Node(exp_node) if exp_node.kind == SyntaxKind::SyntaxQuotation => {
                        if let Some(content) = exp_node.children.first() {
                            content.clone()
                        } else {
                            expanded
                        }
                    }
                    _ => expanded,
                };

                return Ok(Some(final_expansion));
            }
        }

        Ok(None)
    }

    /// Try to expand a node as a macro application
    fn try_expand_macro(
        &self,
        node: &SyntaxNode,
        _ctx: &HygieneContext,
    ) -> ExpansionResult<Option<Syntax>> {
        let (macro_name, _is_app) = match node.kind {
            SyntaxKind::App => {
                // Macro application like (App panic! "msg")
                match node.children.first() {
                    Some(Syntax::Atom(atom)) => (atom.value.as_str(), true),
                    _ => return Ok(None),
                }
            }
            _ => {
                // Not a macro application
                return Ok(None);
            }
        };

        // Look up macro definitions
        let macros = match self.env.get_macros(macro_name) {
            Some(macros) => macros,
            None => return Ok(None),
        };

        // Try each macro definition in order
        for macro_def in macros {
            let pattern_match = if Self::is_macro_rules_pattern(&macro_def.pattern) {
                // For macro_rules, match the entire application against the quoted pattern
                PatternMatcher::match_pattern(
                    &macro_def.pattern,
                    &Syntax::Node(Box::new(node.clone())),
                )?
            } else {
                // For traditional macros with typed parameters, match arguments against
                // parameter pattern
                Self::match_traditional_macro(&macro_def.pattern, node)?
            };

            if let Some(pattern_match) = pattern_match {
                // Substitute into template
                let expanded = substitute_template(&macro_def.template, &pattern_match.bindings)?;

                // If the template result is a SyntaxQuotation, unwrap it for the final
                // expansion
                let final_expansion = match &expanded {
                    Syntax::Node(exp_node) if exp_node.kind == SyntaxKind::SyntaxQuotation => {
                        if let Some(content) = exp_node.children.first() {
                            content.clone()
                        } else {
                            expanded
                        }
                    }
                    _ => expanded,
                };

                return Ok(Some(final_expansion));
            }
        }

        // No matching macro found
        Ok(None)
    }

    /// Expand children of a node
    fn expand_node(&mut self, node: &SyntaxNode, ctx: &HygieneContext) -> ExpansionResult<Syntax> {
        // Special handling for macro definition nodes - don't expand their contents
        match node.kind {
            SyntaxKind::MacroRules | SyntaxKind::MacroDef => {
                // Don't expand the contents of macro definitions, just return them as-is
                // They will be filtered out by the module expansion logic
                return Ok(Syntax::Node(Box::new(node.clone())));
            }
            _ => {}
        }

        let mut new_children = Vec::with_capacity(node.children.len());

        for child in &node.children {
            let expanded = self.expand_with_context(child, ctx)?;
            new_children.push(expanded);
        }

        Ok(Syntax::Node(Box::new(SyntaxNode {
            kind: node.kind,
            range: node.range,
            children: new_children.into(),
        })))
    }

    /// Check if a pattern is from macro_rules (contains SyntaxQuotation)
    fn is_macro_rules_pattern(pattern: &Syntax) -> bool {
        match pattern {
            Syntax::Node(node) => node.kind == SyntaxKind::SyntaxQuotation,
            _ => false,
        }
    }

    /// Match traditional macro with typed parameters against application
    /// arguments
    fn match_traditional_macro(
        pattern: &Syntax,
        app_node: &SyntaxNode,
    ) -> ExpansionResult<Option<crate::pattern::PatternMatch>> {
        // Traditional macro pattern can be:
        // - Syntax::Missing for parameterless macros like unreachable!
        // - (App x term) for single typed parameter x:term
        // - (App (App x term) (App y term)) for multiple parameters x:term y:term

        // Get arguments (skip the first child which is the macro name)
        let args: Vec<&Syntax> = app_node.children.iter().skip(1).collect();

        match pattern {
            Syntax::Missing => {
                // Parameterless macro like unreachable!
                if args.is_empty() {
                    let bindings = im::HashMap::new();
                    return Ok(Some(crate::pattern::PatternMatch { bindings }));
                }
            }
            Syntax::Node(pattern_node) if pattern_node.kind == SyntaxKind::App => {
                // Try to parse as multiple parameters first
                if let Some(bindings) = Self::match_multiple_parameters(pattern_node, &args)? {
                    return Ok(Some(crate::pattern::PatternMatch { bindings }));
                }

                // Fall back to single parameter matching
                if pattern_node.children.len() == 2 && args.len() == 1 {
                    if let (Some(Syntax::Atom(var_name)), Some(Syntax::Atom(_category))) =
                        (pattern_node.children.first(), pattern_node.children.get(1))
                    {
                        // Bind the variable to the argument
                        let mut bindings = im::HashMap::new();
                        bindings.insert(var_name.value.clone(), args[0].clone());
                        return Ok(Some(crate::pattern::PatternMatch { bindings }));
                    }
                }
            }
            _ => {}
        }

        Ok(None)
    }

    /// Match multiple parameters against arguments
    fn match_multiple_parameters(
        pattern_node: &lean_syn_expr::SyntaxNode,
        args: &[&Syntax],
    ) -> ExpansionResult<Option<im::HashMap<eterned::BaseCoword, Syntax>>> {
        // Extract parameter specifications from the pattern
        let params = Self::extract_parameters(pattern_node)?;

        // Check if we have the right number of arguments
        if params.len() != args.len() {
            return Ok(None);
        }

        // Match each parameter against its corresponding argument
        let mut bindings = im::HashMap::new();
        for (param, arg) in params.iter().zip(args.iter()) {
            bindings.insert(param.name.clone(), (*arg).clone());
        }

        Ok(Some(bindings))
    }

    /// Extract parameter specifications from a pattern node
    fn extract_parameters(
        pattern_node: &lean_syn_expr::SyntaxNode,
    ) -> ExpansionResult<Vec<MacroParameter>> {
        let mut params = Vec::new();

        // Pattern can be nested Apps: (App (App x term) (App y term))
        // Or a flat list: (App x term y term)

        if pattern_node.children.len() == 2 {
            // Single parameter: (App x term)
            if let (Some(Syntax::Atom(var_name)), Some(Syntax::Atom(category))) =
                (pattern_node.children.first(), pattern_node.children.get(1))
            {
                params.push(MacroParameter {
                    name: var_name.value.clone(),
                    category: category.value.clone(),
                });
            }
        } else if pattern_node.children.len() > 2 {
            // Multiple parameters in flat form: (App x term y term)
            let mut i = 0;
            while i + 1 < pattern_node.children.len() {
                if let (Some(Syntax::Atom(var_name)), Some(Syntax::Atom(category))) = (
                    pattern_node.children.get(i),
                    pattern_node.children.get(i + 1),
                ) {
                    params.push(MacroParameter {
                        name: var_name.value.clone(),
                        category: category.value.clone(),
                    });
                    i += 2;
                } else {
                    break;
                }
            }
        }

        Ok(params)
    }

    /// Register built-in macros
    pub fn register_builtins(&mut self) {
        use eterned::BaseCoword;
        use lean_syn_expr::{SourcePos, SourceRange, SyntaxAtom, SyntaxNode};

        let dummy_range = SourceRange {
            start: SourcePos::new(0, 0, 0),
            end: SourcePos::new(0, 0, 0),
        };

        // panic! macro: panic! msg => panic msg
        let panic_pattern = Syntax::Node(Box::new(SyntaxNode {
            kind: lean_syn_expr::SyntaxKind::App,
            range: dummy_range,
            children: smallvec![
                Syntax::Atom(SyntaxAtom {
                    range: dummy_range,
                    value: BaseCoword::new("msg")
                }),
                Syntax::Atom(SyntaxAtom {
                    range: dummy_range,
                    value: BaseCoword::new("term")
                }),
            ],
        }));

        let panic_template = Syntax::Node(Box::new(SyntaxNode {
            kind: lean_syn_expr::SyntaxKind::SyntaxQuotation,
            range: dummy_range,
            children: smallvec![Syntax::Node(Box::new(SyntaxNode {
                kind: lean_syn_expr::SyntaxKind::App,
                range: dummy_range,
                children: smallvec![
                    Syntax::Atom(SyntaxAtom {
                        range: dummy_range,
                        value: BaseCoword::new("panic")
                    }),
                    Syntax::Node(Box::new(SyntaxNode {
                        kind: lean_syn_expr::SyntaxKind::SyntaxAntiquotation,
                        range: dummy_range,
                        children: smallvec![Syntax::Atom(SyntaxAtom {
                            range: dummy_range,
                            value: BaseCoword::new("msg")
                        }),],
                    })),
                ],
            })),],
        }));

        let panic_macro = crate::environment::MacroDefinition {
            name: BaseCoword::new("panic!"),
            pattern: panic_pattern,
            template: panic_template,
            category: BaseCoword::new("term"),
            priority: 0,
        };

        self.env.register_macro(panic_macro);

        // unreachable! macro: unreachable! => panic "unreachable code"
        let unreachable_template = Syntax::Node(Box::new(SyntaxNode {
            kind: lean_syn_expr::SyntaxKind::SyntaxQuotation,
            range: dummy_range,
            children: smallvec![Syntax::Node(Box::new(SyntaxNode {
                kind: lean_syn_expr::SyntaxKind::App,
                range: dummy_range,
                children: smallvec![
                    Syntax::Atom(SyntaxAtom {
                        range: dummy_range,
                        value: BaseCoword::new("panic")
                    }),
                    Syntax::Atom(SyntaxAtom {
                        range: dummy_range,
                        value: BaseCoword::new("\"unreachable code\"")
                    }),
                ],
            })),],
        }));

        // unreachable! has no parameters
        let unreachable_pattern = Syntax::Missing;

        let unreachable_macro = crate::environment::MacroDefinition {
            name: BaseCoword::new("unreachable!"),
            pattern: unreachable_pattern,
            template: unreachable_template,
            category: BaseCoword::new("term"),
            priority: 0,
        };

        self.env.register_macro(unreachable_macro);

        // assert! macro: assert! cond => if cond then () else panic "assertion failed"
        let assert_pattern = Syntax::Node(Box::new(SyntaxNode {
            kind: lean_syn_expr::SyntaxKind::App,
            range: dummy_range,
            children: smallvec![
                Syntax::Atom(SyntaxAtom {
                    range: dummy_range,
                    value: BaseCoword::new("cond")
                }),
                Syntax::Atom(SyntaxAtom {
                    range: dummy_range,
                    value: BaseCoword::new("term")
                }),
            ],
        }));

        let assert_template = Syntax::Node(Box::new(SyntaxNode {
            kind: lean_syn_expr::SyntaxKind::SyntaxQuotation,
            range: dummy_range,
            children: smallvec![Syntax::Node(Box::new(SyntaxNode {
                kind: lean_syn_expr::SyntaxKind::App,
                range: dummy_range,
                children: smallvec![
                    Syntax::Atom(SyntaxAtom {
                        range: dummy_range,
                        value: BaseCoword::new("if")
                    }),
                    Syntax::Node(Box::new(SyntaxNode {
                        kind: lean_syn_expr::SyntaxKind::SyntaxAntiquotation,
                        range: dummy_range,
                        children: smallvec![Syntax::Atom(SyntaxAtom {
                            range: dummy_range,
                            value: BaseCoword::new("cond")
                        }),],
                    })),
                    Syntax::Atom(SyntaxAtom {
                        range: dummy_range,
                        value: BaseCoword::new("then")
                    }),
                    Syntax::Atom(SyntaxAtom {
                        range: dummy_range,
                        value: BaseCoword::new("()")
                    }),
                    Syntax::Atom(SyntaxAtom {
                        range: dummy_range,
                        value: BaseCoword::new("else")
                    }),
                    Syntax::Node(Box::new(SyntaxNode {
                        kind: lean_syn_expr::SyntaxKind::App,
                        range: dummy_range,
                        children: smallvec![
                            Syntax::Atom(SyntaxAtom {
                                range: dummy_range,
                                value: BaseCoword::new("panic")
                            }),
                            Syntax::Atom(SyntaxAtom {
                                range: dummy_range,
                                value: BaseCoword::new("\"assertion failed\"")
                            }),
                        ],
                    })),
                ],
            })),],
        }));

        let assert_macro = crate::environment::MacroDefinition {
            name: BaseCoword::new("assert!"),
            pattern: assert_pattern,
            template: assert_template,
            category: BaseCoword::new("term"),
            priority: 0,
        };

        self.env.register_macro(assert_macro);

        // dbg! macro: dbg! expr => let tmp := expr; trace! tmp; tmp
        // The dbg! macro prints the expression and returns its value
        let dbg_pattern = Syntax::Node(Box::new(SyntaxNode {
            kind: lean_syn_expr::SyntaxKind::App,
            range: dummy_range,
            children: smallvec![
                Syntax::Atom(SyntaxAtom {
                    range: dummy_range,
                    value: BaseCoword::new("expr")
                }),
                Syntax::Atom(SyntaxAtom {
                    range: dummy_range,
                    value: BaseCoword::new("term")
                }),
            ],
        }));

        // For now, just return the expression itself since we don't have trace! yet
        // In a full implementation, this would: let tmp := expr; trace! tmp; tmp
        let dbg_template = Syntax::Node(Box::new(SyntaxNode {
            kind: lean_syn_expr::SyntaxKind::SyntaxQuotation,
            range: dummy_range,
            children: smallvec![Syntax::Node(Box::new(SyntaxNode {
                kind: lean_syn_expr::SyntaxKind::SyntaxAntiquotation,
                range: dummy_range,
                children: smallvec![Syntax::Atom(SyntaxAtom {
                    range: dummy_range,
                    value: BaseCoword::new("expr")
                }),],
            })),],
        }));

        let dbg_macro = crate::environment::MacroDefinition {
            name: BaseCoword::new("dbg!"),
            pattern: dbg_pattern,
            template: dbg_template,
            category: BaseCoword::new("term"),
            priority: 0,
        };

        self.env.register_macro(dbg_macro);
    }
}

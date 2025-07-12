//! Tests for whitespace and comment preservation (trivia support)

use crate::parser::Parser;
use lean_syn_expr::{Syntax, TriviaKind};

/// Test that whitespace is preserved as leading trivia
#[test]
fn test_whitespace_preservation() {
    let input = "   hello";
    let mut parser = Parser::new(input);
    
    let result = parser.identifier().unwrap();
    
    if let Syntax::Atom(atom) = result {
        assert_eq!(atom.value.as_str(), "hello");
        assert_eq!(atom.leading_trivia.len(), 1);
        assert_eq!(atom.leading_trivia[0].kind, TriviaKind::Whitespace);
        assert_eq!(atom.leading_trivia[0].text, "   ");
        assert!(atom.trailing_trivia.is_empty());
    } else {
        panic!("Expected atom, got: {:?}", result);
    }
}

/// Test that line comments are preserved as trivia
#[test]
fn test_line_comment_preservation() {
    let input = "-- This is a comment\nhello";
    let mut parser = Parser::new(input);
    
    let result = parser.identifier().unwrap();
    
    if let Syntax::Atom(atom) = result {
        assert_eq!(atom.value.as_str(), "hello");
        assert_eq!(atom.leading_trivia.len(), 2); // comment + newline
        assert_eq!(atom.leading_trivia[0].kind, TriviaKind::LineComment);
        assert_eq!(atom.leading_trivia[0].text, "-- This is a comment");
        assert_eq!(atom.leading_trivia[1].kind, TriviaKind::Whitespace);
        assert_eq!(atom.leading_trivia[1].text, "\n");
    } else {
        panic!("Expected atom, got: {:?}", result);
    }
}

/// Test that block comments are preserved as trivia
#[test]
fn test_block_comment_preservation() {
    let input = "/* block comment */ hello";
    let mut parser = Parser::new(input);
    
    let result = parser.identifier().unwrap();
    
    if let Syntax::Atom(atom) = result {
        assert_eq!(atom.value.as_str(), "hello");
        assert_eq!(atom.leading_trivia.len(), 2); // comment + space
        assert_eq!(atom.leading_trivia[0].kind, TriviaKind::BlockComment);
        assert_eq!(atom.leading_trivia[0].text, "/* block comment */");
        assert_eq!(atom.leading_trivia[1].kind, TriviaKind::Whitespace);
        assert_eq!(atom.leading_trivia[1].text, " ");
    } else {
        panic!("Expected atom, got: {:?}", result);
    }
}

/// Test that doc comments are preserved as trivia
#[test]
fn test_doc_comment_preservation() {
    let input = "/-- Documentation comment --/ hello";
    let mut parser = Parser::new(input);
    
    let result = parser.identifier().unwrap();
    
    if let Syntax::Atom(atom) = result {
        assert_eq!(atom.value.as_str(), "hello");
        assert_eq!(atom.leading_trivia.len(), 2); // doc comment + space
        assert_eq!(atom.leading_trivia[0].kind, TriviaKind::DocComment);
        assert_eq!(atom.leading_trivia[0].text, "/-- Documentation comment --/");
        assert_eq!(atom.leading_trivia[1].kind, TriviaKind::Whitespace);
        assert_eq!(atom.leading_trivia[1].text, " ");
    } else {
        panic!("Expected atom, got: {:?}", result);
    }
}

/// Test mixed whitespace and comments
#[test]
fn test_mixed_trivia_preservation() {
    let input = "  \n-- comment\n  /* block */  hello";
    let mut parser = Parser::new(input);
    
    let result = parser.identifier().unwrap();
    
    if let Syntax::Atom(atom) = result {
        assert_eq!(atom.value.as_str(), "hello");
        assert!(atom.leading_trivia.len() >= 4); // At least whitespace, newline, comment, block comment
        
        // Check that we have the expected trivia types
        let has_whitespace = atom.leading_trivia.iter().any(|t| t.kind == TriviaKind::Whitespace);
        let has_line_comment = atom.leading_trivia.iter().any(|t| t.kind == TriviaKind::LineComment);
        let has_block_comment = atom.leading_trivia.iter().any(|t| t.kind == TriviaKind::BlockComment);
        
        assert!(has_whitespace, "Should have whitespace trivia");
        assert!(has_line_comment, "Should have line comment trivia");
        assert!(has_block_comment, "Should have block comment trivia");
    } else {
        panic!("Expected atom, got: {:?}", result);
    }
}

/// Test that trivia is preserved in complex expressions
#[test]
fn test_trivia_in_expressions() {
    let input = "  /* comment */ def  hello : Nat := 42";
    let mut parser = Parser::new(input);
    
    let result = parser.def_command().unwrap();
    
    if let Syntax::Node(node) = result {
        assert!(!node.leading_trivia.is_empty(), "Node should have leading trivia");
        
        // Check that the first child (def keyword) has trivia
        if let Some(Syntax::Atom(def_atom)) = node.children.first() {
            assert!(!def_atom.leading_trivia.is_empty(), "Def keyword should have leading trivia");
        }
    } else {
        panic!("Expected node, got: {:?}", result);
    }
}

/// Test that Unicode operators work with trivia preservation
#[test]
fn test_unicode_operators_with_trivia() {
    let input = "  a ∈ b";  // Unicode set membership operator
    let mut parser = Parser::new(input);
    
    let result = parser.term().unwrap();
    
    if let Syntax::Node(node) = result {
        assert!(!node.leading_trivia.is_empty(), "Should have leading trivia");
        
        // Should parse as binary operation with ∈ operator
        assert_eq!(node.children.len(), 3); // a, ∈, b
        
        if let Some(Syntax::Atom(op_atom)) = node.children.get(1) {
            assert_eq!(op_atom.value.as_str(), "∈");
        }
    } else {
        panic!("Expected binary operation node, got: {:?}", result);
    }
}

/// Test that trivia is preserved across multiple tokens
#[test]
fn test_trivia_preservation_across_tokens() {
    let input = "hello  /* comment */  world";
    let mut parser = Parser::new(input);
    
    // Parse first identifier
    let first = parser.identifier().unwrap();
    if let Syntax::Atom(atom) = first {
        assert_eq!(atom.value.as_str(), "hello");
    }
    
    // Parse second identifier - should have trivia from between tokens
    let second = parser.identifier().unwrap();
    if let Syntax::Atom(atom) = second {
        assert_eq!(atom.value.as_str(), "world");
        assert!(!atom.leading_trivia.is_empty(), "Second token should have trivia");
        
        // Should contain the comment and whitespace
        let has_comment = atom.leading_trivia.iter().any(|t| t.kind == TriviaKind::BlockComment);
        assert!(has_comment, "Should preserve block comment between tokens");
    }
}

/// Test that empty trivia lists work correctly
#[test]
fn test_no_trivia() {
    let input = "hello";
    let mut parser = Parser::new(input);
    
    let result = parser.identifier().unwrap();
    
    if let Syntax::Atom(atom) = result {
        assert_eq!(atom.value.as_str(), "hello");
        assert!(atom.leading_trivia.is_empty(), "Should have no leading trivia");
        assert!(atom.trailing_trivia.is_empty(), "Should have no trailing trivia");
    } else {
        panic!("Expected atom, got: {:?}", result);
    }
}

/// Test that trivia is correctly attached to syntax nodes
#[test]
fn test_trivia_attachment_to_nodes() {
    let input = "  \n-- Comment\ndef foo := 42";
    let mut parser = Parser::new(input);
    
    let result = parser.def_command().unwrap();
    
    if let Syntax::Node(node) = result {
        // The definition node itself should have the leading trivia
        assert!(!node.leading_trivia.is_empty(), "Definition node should have leading trivia");
        
        // Check that trivia contains whitespace and comment
        let trivia_text: String = node.leading_trivia.iter().map(|t| t.text.as_str()).collect();
        assert!(trivia_text.contains("-- Comment"), "Should contain line comment");
    } else {
        panic!("Expected definition node, got: {:?}", result);
    }
}
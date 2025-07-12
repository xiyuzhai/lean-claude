//! Common lexical helpers for the parser

/// Check if a character can start an identifier
///
/// According to Unicode standards and Lean 4 spec, identifiers can start with:
/// - Letter characters (Unicode categories Lu, Ll, Lt, Lm, Lo)
/// - Underscore (_)
/// - Some mathematical symbols commonly used in Lean
pub fn is_id_start(ch: char) -> bool {
    // Standard Unicode letter categories
    if ch.is_alphabetic() {
        return true;
    }

    // Underscore is always allowed
    if ch == '_' {
        return true;
    }

    // Greek letters commonly used in mathematics
    if ('\u{0370}'..='\u{03FF}').contains(&ch) {
        // Greek and Coptic
        return true;
    }

    // Mathematical symbols that are commonly used as identifiers in Lean
    match ch {
        // Mathematical script letters
        '\u{1D49C}'..='\u{1D4CF}' |  // Mathematical Script
        '\u{1D4D0}'..='\u{1D503}' |  // Mathematical Bold Script
        '\u{1D504}'..='\u{1D537}' |  // Mathematical Fraktur
        '\u{1D538}'..='\u{1D56B}' |  // Mathematical Double-Struck
        '\u{1D56C}'..='\u{1D59F}' |  // Mathematical Bold Fraktur
        '\u{1D5A0}'..='\u{1D5D3}' |  // Mathematical Sans-Serif
        '\u{1D5D4}'..='\u{1D607}' |  // Mathematical Sans-Serif Bold
        '\u{1D608}'..='\u{1D63B}' |  // Mathematical Sans-Serif Italic
        '\u{1D63C}'..='\u{1D66F}' |  // Mathematical Sans-Serif Bold Italic
        '\u{1D670}'..='\u{1D6A3}' |  // Mathematical Monospace
        // Commonly used mathematical symbols
        'α' | 'β' | 'γ' | 'δ' | 'ε' | 'ζ' | 'η' | 'θ' | 'ι' | 'κ' | 'λ' | 'μ' |
        'ν' | 'ξ' | 'ο' | 'π' | 'ρ' | 'σ' | 'τ' | 'υ' | 'φ' | 'χ' | 'ψ' | 'ω' |
        'Α' | 'Β' | 'Γ' | 'Δ' | 'Ε' | 'Ζ' | 'Η' | 'Θ' | 'Ι' | 'Κ' | 'Λ' | 'Μ' |
        'Ν' | 'Ξ' | 'Ο' | 'Π' | 'Ρ' | 'Σ' | 'Τ' | 'Υ' | 'Φ' | 'Χ' | 'Ψ' | 'Ω' => true,
        _ => false,
    }
}

/// Check if a character can continue an identifier
///
/// Identifiers can continue with:
/// - All characters that can start an identifier
/// - Digits (Unicode category Nd)
/// - Underscore, apostrophe, question mark, exclamation mark
/// - Mathematical subscripts and superscripts
pub fn is_id_continue(ch: char) -> bool {
    // Can continue with anything that can start
    if is_id_start(ch) {
        return true;
    }

    // Digits are allowed
    if ch.is_ascii_digit() {
        return true;
    }

    // Unicode digit categories
    if ch.is_numeric() {
        return true;
    }

    // Special Lean identifier continuation characters
    if matches!(ch, '_' | '\'' | '?' | '!') {
        return true;
    }

    // Mathematical subscripts and superscripts
    match ch {
        '\u{2070}'..='\u{207F}' |  // Superscripts and Subscripts
        '\u{2080}'..='\u{209F}' |  // Subscripts
        '\u{1D62C}'..='\u{1D66F}' | // Mathematical Monospace digits
        '₀'..='₉' |                 // Subscript digits
        '⁰'..='⁹' => true,          // Superscript digits
        _ => false,
    }
}

/// Check if a character is a valid Unicode operator character
///
/// This includes mathematical symbols that can be used as operators
pub fn is_operator_char(ch: char) -> bool {
    match ch {
        // Basic ASCII operators
        '+' | '-' | '*' | '/' | '%' | '^' | '&' | '|' | '=' | '<' | '>' |
        '!' | '?' | ':' | '.' | '~' | '@' | '#' | '$' => true,
        // Mathematical operators (Unicode categories Sm, So)
        '\u{2200}'..='\u{22FF}' |  // Mathematical Operators
        '\u{2A00}'..='\u{2AFF}' |  // Supplemental Mathematical Operators
        '\u{27C0}'..='\u{27EF}' |  // Miscellaneous Mathematical Symbols-A
        '\u{2980}'..='\u{29FF}' |  // Miscellaneous Mathematical Symbols-B
        '\u{2190}'..='\u{21FF}' |  // Arrows
        '\u{2300}'..='\u{23FF}' |  // Miscellaneous Technical

        // Specific commonly used mathematical symbols
        '∀' | '∃' | '∄' | '∅' | '∆' | '∇' | '∈' | '∉' | '∋' | '∌' | '∏' | '∐' |
        '∑' | '√' | '∝' | '∞' | '∟' | '∠' | '∡' | '∢' | '∣' | '∤' | '∥' | '∦' |
        '∧' | '∨' | '∩' | '∪' | '∫' | '∬' | '∭' | '∮' | '∯' | '∰' | '∱' | '∲' |
        '∳' | '∴' | '∵' | '∶' | '∷' | '∸' | '∹' | '∺' | '∻' | '∼' | '∽' | '∾' |
        '∿' | '≀' | '≁' | '≂' | '≃' | '≄' | '≅' | '≆' | '≇' | '≈' | '≉' | '≊' |
        '≋' | '≌' | '≍' | '≎' | '≏' | '≐' | '≑' | '≒' | '≓' | '≔' | '≕' | '≖' |
        '≗' | '≘' | '≙' | '≚' | '≛' | '≜' | '≝' | '≞' | '≟' | '≠' | '≡' | '≢' |
        '≣' | '≤' | '≥' | '≦' | '≧' | '≨' | '≩' | '≪' | '≫' | '≬' | '≭' | '≮' |
        '≯' | '≰' | '≱' | '≲' | '≳' | '≴' | '≵' | '≶' | '≷' | '≸' | '≹' | '≺' |
        '≻' | '≼' | '≽' | '≾' | '≿' | '⊀' | '⊁' | '⊂' | '⊃' | '⊄' | '⊅' | '⊆' |
        '⊇' | '⊈' | '⊉' | '⊊' | '⊋' | '⊌' | '⊍' | '⊎' | '⊏' | '⊐' | '⊑' | '⊒' |
        '⊓' | '⊔' | '⊕' | '⊖' | '⊗' | '⊘' | '⊙' | '⊚' | '⊛' | '⊜' | '⊝' | '⊞' |
        '⊟' | '⊠' | '⊡' | '⊢' | '⊣' | '⊤' | '⊥' | '⊦' | '⊧' | '⊨' | '⊩' | '⊪' |
        '⊫' | '⊬' | '⊭' | '⊮' | '⊯' | '⊰' | '⊱' | '⊲' | '⊳' | '⊴' | '⊵' | '⊶' |
        '⊷' | '⊸' | '⊹' | '⊺' | '⊻' | '⊼' | '⊽' | '⊾' | '⊿' | 
        
        // Arrows
        '←' | '↑' | '→' | '↓' | '↔' | '↕' | '↖' | '↗' | '↘' | '↙' | '↚' | '↛' |
        '↜' | '↝' | '↞' | '↟' | '↠' | '↡' | '↢' | '↣' | '↤' | '↥' | '↦' | '↧' |
        '↨' | '↩' | '↪' | '↫' | '↬' | '↭' | '↮' | '↯' | '↰' | '↱' | '↲' | '↳' |
        '↴' | '↵' | '↶' | '↷' | '↸' | '↹' | '↺' | '↻' | '↼' | '↽' | '↾' | '↿' |
        '⇀' | '⇁' | '⇂' | '⇃' | '⇄' | '⇅' | '⇆' | '⇇' | '⇈' | '⇉' | '⇊' | '⇋' |
        '⇌' | '⇍' | '⇎' | '⇏' | '⇐' | '⇑' | '⇒' | '⇓' | '⇔' | '⇕' | '⇖' | '⇗' |
        '⇘' | '⇙' | '⇚' | '⇛' | '⇜' | '⇝' | '⇞' | '⇟' | '⇠' | '⇡' | '⇢' | '⇣' |
        '⇤' | '⇥' | '⇦' | '⇧' | '⇨' | '⇩' | '⇪' | '⇫' | '⇬' | '⇭' | '⇮' | '⇯' |
        '⇰' | '⇱' | '⇲' | '⇳' | '⇴' | '⇵' | '⇶' | '⇷' | '⇸' | '⇹' | '⇺' | '⇻' |
        '⇼' | '⇽' | '⇾' | '⇿' |
        
        // Mathematical symbols
        '×' | '÷' | '±' | '∓' | '∘' | '∙' | '√' | '∛' | '∜' | '∝' | '∞' | '∟' |
        '∠' | '∡' | '∢' | '∣' | '∤' | '∥' | '∦' | '∧' | '∨' | '∩' | '∪' | '∫' |
        '∬' | '∭' | '∮' | '∯' | '∰' | '∱' | '∲' | '∳' => true,
        
        _ => false,
    }
}

/// Common lexical helpers for the parser

/// Check if a character can start an identifier
pub fn is_id_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

/// Check if a character can continue an identifier
pub fn is_id_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '?' || ch == '!'
}

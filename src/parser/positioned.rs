use crate::token::{Expect, TokenKind};

enum ParseErrorKind {
    Expected {
        expected: Expect,
        found: Option<TokenKind>,
    },
}

struct ParseError {
    kind: ParseErrorKind,
    pos: usize,
    len: usize,
}

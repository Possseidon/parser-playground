use std::num::NonZeroUsize;

pub(crate) struct PositionedLexer<'code> {
    code: &'code str,
    pos: usize,
    errors: Vec<PositionedLexerError>,
}

impl<'code> PositionedLexer<'code> {
    /// To figure out initally skipped whitespace, simply call [`Self::pos()`] immediately.
    pub(crate) fn new(code: &'code str) -> Self {
        let mut result = Self {
            code,
            pos: 0,
            errors: Vec::new(),
        };
        // result.advance();
        result
    }

    pub(crate) fn pos(&self) -> usize {
        self.pos
    }

    pub(crate) fn take_errors(self) -> Vec<PositionedLexerError> {
        self.errors
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct PositionedLexerToken {
    pub(crate) pos: usize,
    pub(crate) len: NonZeroUsize,
    pub(crate) trailing_whitespace_len: usize,
}

/// Some error that occured during lexing.
pub(crate) enum LexerError {}

/// A [`LexerError`] enhanced with position information.
pub(crate) struct PositionedLexerError {
    pub(crate) error: LexerError,
    pub(crate) from: usize,
    pub(crate) to: usize,
}

impl Iterator for PositionedLexer<'_> {
    type Item = PositionedLexerToken;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

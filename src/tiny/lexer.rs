use smol_str::SmolStr;

use crate::{
    lexer::{
        lex_char_or_label, lex_doc_comment, lex_integer_or_float, lex_keyword_or_ident, lex_quoted,
        lex_raw_string, trim_whitespace, LexerToken,
    },
    token::{FixedTokenKind, Tiny},
};

use super::TinyError;

#[derive(Debug)]
pub(crate) struct TinyLexer<'code> {
    code: &'code str,
}

impl<'code> TinyLexer<'code> {
    pub(crate) fn new(code: &'code str) -> Result<Self, TinyError> {
        Ok(TinyLexer {
            code: trim_whitespace(code).map_err(|_| TinyError)?,
        })
    }

    /// Yields the next token, assuming whitespace was skipped already.
    pub(crate) fn next_token(&mut self) -> Result<LexerToken<Tiny>, TinyError> {
        let (kind, len) = if let Some(kind_len) = lex_doc_comment(self.code) {
            kind_len
        } else if let Some(kind_len) = lex_integer_or_float(self.code) {
            kind_len
        } else if let Some(kind_len) = lex_char_or_label(self.code).map_err(|_| TinyError)? {
            kind_len
        } else if let Some(kind_len) = lex_quoted(self.code).map_err(|_| TinyError)? {
            kind_len
        } else if let Some(kind_len) = lex_raw_string(self.code).map_err(|_| TinyError)? {
            kind_len
        } else if let Some(kind_len) = lex_keyword_or_ident(self.code) {
            kind_len
        } else if let Some((kind, len)) = FixedTokenKind::parse_symbol(self.code.as_bytes()) {
            (kind.into(), len)
        } else if let Some(kind) = FixedTokenKind::parse_char(self.code.as_bytes()[0]) {
            (kind.into(), 1)
        } else {
            return Err(TinyError);
        };

        let token = if kind.is_dynamic() {
            self.code[..len].into()
        } else {
            SmolStr::default()
        };

        self.code = &self.code[len..];
        Ok(LexerToken { kind, token })
    }
}

impl Iterator for TinyLexer<'_> {
    type Item = Result<LexerToken<Tiny>, TinyError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.code.is_empty() {
            return None;
        }

        match self.next_token() {
            Ok(token) => {
                let Ok(rest) = trim_whitespace(self.code) else {
                    return Some(Err(TinyError));
                };
                self.code = rest;
                Some(Ok(token))
            }
            Err(error) => Some(Err(TinyError)),
        }
    }
}

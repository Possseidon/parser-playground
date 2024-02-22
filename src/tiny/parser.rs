use bitvec::vec::BitVec;
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::{
    lexer::CheckedLexer,
    parser::{ExpectedTokens, ParseImpl},
    token::{Expect, Tiny},
};

use super::{lexer::TinyLexer, TinyError};

pub(crate) trait ParseFastImpl: Sized {
    /// Used by [`TinyParse::tiny_parse_fast()`].
    fn parse_nested(lexer: &mut CheckedLexer<Tiny>, expect: Expect) -> Result<Self, TinyError>;
}

/// Allows parsing recursively, which might stack overflow.
pub(crate) trait ParseFast: ParseImpl<Tiny> + ParseFastImpl {
    /// Parses recursively.
    ///
    /// This is very fast, but might lead to a stack overflow for deeply nested code. To avoid
    /// crashes for e.g. untrusted input, use [`parser::Parse::parse()`].
    ///
    /// One could add a `max_recursion` limit here, but that can't really provide any guarantees,
    /// since the stack might already be almost full despite a low limit.
    ///
    /// Additionally, I would have to duplicate a bunch of code, since I don't want this recursion
    /// check to slow down parsing (even though it probably wouldn't be much). I might look into
    /// this again in the future, but for now I'll keep it as is.
    fn parse_fast(code: &str) -> Result<Self, TinyError> {
        let lexer = TinyLexer::new(code);
        let mut lexer = CheckedLexer::new(lexer, Self::INITIAL_EXPECT)?;
        Self::parse_nested(&mut lexer, Expect::END_OF_INPUT)
    }
}

impl<T: ParseImpl<Tiny> + ParseFastImpl> ParseFast for T {}

/// A stack of tokens which might be optionals or repetitions.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct TinyTokenStack {
    /// A stack of all dynamic tokens such as identifiers.
    dynamic_tokens: Vec<SmolStr>,
    /// Pushed for optional elements; `true` meaning `Some` and `false` meaning `None`.
    ///
    /// For existing dynamic tokens, there will be a matching entry in [`Self::dynamic_tokens`].
    optionals: BitVec,
    /// Contains the counts of a fixed token repetition.
    fixed_repetitions: SmallVec<[usize; 2]>,
    /// Contains the start index into [`Self::dynamic_tokens`] of a list of dynamic tokens.
    dynamic_repetitions: SmallVec<[usize; 2]>,
}

impl TinyTokenStack {
    /// Consumes [`self`] and returns if the stack is empty, which should always be the case at the
    /// end of parsing.
    pub(crate) fn finish(self) -> bool {
        self.dynamic_tokens.is_empty()
            && self.optionals.is_empty()
            && self.fixed_repetitions.is_empty()
            && self.dynamic_repetitions.is_empty()
    }

    /// Pushes a dynamic token like an identifier.
    pub(crate) fn push_dynamic(&mut self, token: SmolStr) {
        self.dynamic_tokens.push(token);
    }

    /// Pops a dynamic token like an identifier.
    pub(crate) fn pop_dynamic(&mut self) -> SmolStr {
        self.dynamic_tokens
            .pop()
            .expect("token stack should not be empty")
    }

    /// Pushes an optional dynamic token that exists.
    pub(crate) fn push_dynamic_some(&mut self, token: SmolStr) {
        self.push_fixed_some();
        self.push_dynamic(token);
    }

    /// Pushes a flag indicating a fixed optional token that exists.
    pub(crate) fn push_fixed_some(&mut self) {
        self.optionals.push(true);
    }

    /// Pushes a flag indicating an optional token that does not exist.
    pub(crate) fn push_none(&mut self) {
        self.optionals.push(false);
    }

    /// Pops an optional dynamic token.
    pub(crate) fn pop_dynamic_optional(&mut self) -> Option<SmolStr> {
        self.pop_fixed_optional().then(|| self.pop_dynamic())
    }

    /// Pops an optional fixed token.
    pub(crate) fn pop_fixed_optional(&mut self) -> bool {
        self.optionals
            .pop()
            .expect("optional stack should not be empty")
    }

    /// Marks the start of a new repetition of dynamic tokens.
    pub(crate) fn start_dynamic_repetition(&mut self) {
        self.dynamic_repetitions.push(self.dynamic_tokens.len());
    }

    /// Pops a repetition of dynamic tokens.
    pub(crate) fn pop_dynamic_repetition(&mut self) -> impl ExactSizeIterator<Item = SmolStr> + '_ {
        self.dynamic_tokens.drain(
            self.dynamic_repetitions
                .pop()
                .expect("dynamic repetition stack should not be empty")..,
        )
    }

    /// Pushes the number of repeating fixed tokens.
    pub(crate) fn push_fixed_repetition(&mut self, count: usize) {
        self.fixed_repetitions.push(count);
    }

    /// Pops the number of repeating fixed tokens.
    pub(crate) fn pop_fixed_repetition(&mut self) -> usize {
        self.fixed_repetitions
            .pop()
            .expect("fixed repetition stack should not be empty")
    }
}

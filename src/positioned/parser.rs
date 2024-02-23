use std::num::NonZeroUsize;

use bitvec::vec::BitVec;

use crate::token::{
    FixedOptionalTokenSpan, FixedRepetitionTokenSpan, FixedTokenSpan, OptionalTokenSpan,
    RepetitionTokenSpan, TokenSpan,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct PositionedTokenStack {
    data: Vec<usize>,
    optionals: BitVec,
}

impl PositionedTokenStack {
    pub(crate) fn finish(self) -> bool {
        self.data.is_empty() && self.optionals.is_empty()
    }

    pub(crate) fn push_fixed<const N: usize>(&mut self, token: FixedTokenSpan<N>) {
        self.data.push(token.pos);
    }

    pub(crate) fn pop_fixed<const N: usize>(&mut self) -> FixedTokenSpan<N> {
        FixedTokenSpan { pos: self.pop() }
    }

    pub(crate) fn push_fixed_optional<const N: usize>(&mut self, token: FixedOptionalTokenSpan<N>) {
        self.optionals.push(token.some);
        self.data.push(token.pos);
    }

    pub(crate) fn pop_fixed_optional<const N: usize>(&mut self) -> FixedOptionalTokenSpan<N> {
        FixedOptionalTokenSpan {
            pos: self.pop(),
            some: self.pop_optional(),
        }
    }

    pub(crate) fn push_fixed_repetition<const N: usize>(
        &mut self,
        repetition: FixedRepetitionTokenSpan<N>,
    ) {
        self.data
            .extend(repetition.tokens.iter().rev().map(|token| token.pos));
        self.data.push(repetition.tokens.len());
        self.data.push(repetition.pos);
    }

    pub(crate) fn pop_fixed_repetition<const N: usize>(&mut self) -> FixedRepetitionTokenSpan<N> {
        FixedRepetitionTokenSpan {
            pos: self.pop(),
            tokens: {
                (0..self.pop())
                    .map(|_| FixedTokenSpan { pos: self.pop() })
                    .collect()
            },
        }
    }

    pub(crate) fn push_dynamic(&mut self, token: TokenSpan) {
        self.data.push(token.len.into());
        self.data.push(token.pos);
    }

    pub(crate) fn pop_dynamic(&mut self) -> TokenSpan {
        TokenSpan {
            pos: self.pop(),
            len: self.pop_len(),
        }
    }

    pub(crate) fn push_dynamic_optional(&mut self, token: OptionalTokenSpan) {
        if let Some(len) = token.len {
            self.data.push(len.into());
        }
        self.optionals.push(token.len.is_some());
        self.data.push(token.pos);
    }

    pub(crate) fn pop_dynamic_optional(&mut self) -> OptionalTokenSpan {
        OptionalTokenSpan {
            pos: self.data.pop().expect("data stack should not be empty"),
            len: self.pop_optional().then(|| self.pop_len()),
        }
    }

    pub(crate) fn push_dynamic_repetition(&mut self, repetition: RepetitionTokenSpan) {
        self.data.extend(
            repetition
                .tokens
                .iter()
                .rev()
                .flat_map(|token| [token.len.into(), token.pos]),
        );
        self.data.push(repetition.tokens.len());
        self.data.push(repetition.pos);
    }

    pub(crate) fn pop_dynamic_repetition(&mut self) -> RepetitionTokenSpan {
        RepetitionTokenSpan {
            pos: self.pop(),
            tokens: {
                (0..self.pop())
                    .map(|_| TokenSpan {
                        pos: self.pop(),
                        len: self.pop_len(),
                    })
                    .collect()
            },
        }
    }

    fn pop(&mut self) -> usize {
        self.data.pop().expect("data stack should not be empty")
    }

    fn pop_len(&mut self) -> NonZeroUsize {
        self.pop().try_into().unwrap()
    }

    fn pop_optional(&mut self) -> bool {
        self.optionals
            .pop()
            .expect("optionals stack should not be empty")
    }
}

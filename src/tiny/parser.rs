use bitvec::vec::BitVec;
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::{
    parser::{NodeStack, ParseImpl},
    tiny::{lexer::CheckedTinyLexer, TinyResult},
    token::{Expect, Tiny},
};

use super::lexer::TinyLexer;

/// A single iterative parsing step.
#[derive(Clone, Copy, Debug)]
struct TinyParseFn<'code> {
    parse: fn(
        state: &mut TinyParseState<'code>,
        expect: Expect,
        field: usize,
        repetition: bool,
    ) -> TinyResult<()>,
    expect: Expect,
    field: usize,
    repetition: bool,
}

impl<'code> TinyParseFn<'code> {
    /// Calls the `parse` function.
    fn parse(self, state: &mut TinyParseState<'code>) -> TinyResult<()> {
        (self.parse)(state, self.expect, self.field, self.repetition)
    }
}

/// The state of an iterative parsing process.
///
/// Consists of a token stream and stacks for parsing steps, tokens and nodes.
#[derive(Debug)]
pub(crate) struct TinyParseState<'code> {
    parsers: Vec<TinyParseFn<'code>>,
    pub(crate) lexer: CheckedTinyLexer<'code>,
    pub(crate) tokens: TinyTokenStack,
    pub(crate) nodes: NodeStack<Tiny>,
}

impl<'code> TinyParseState<'code> {
    /// Creates a new parsing state from a token stream.
    pub(crate) fn new(lexer: CheckedTinyLexer<'code>) -> Self {
        Self {
            parsers: Vec::new(),
            lexer,
            tokens: TinyTokenStack::new(),
            nodes: NodeStack::new(),
        }
    }

    /// Pushes a new parsing step for a normal node.
    pub(crate) fn push_parser<N: TinyParseImpl>(&mut self, expect: Expect) {
        self.parsers.push(TinyParseFn {
            parse: N::tiny_parse_iterative,
            expect,
            field: 0,
            repetition: false,
        })
    }

    /// Pushes a new parsing step for building an alternation.
    pub(crate) fn push_build_enum<N: TinyParseImpl>(&mut self, expect: Expect) {
        self.parsers.push(TinyParseFn {
            parse: N::tiny_parse_iterative,
            expect,
            field: 1,
            repetition: false,
        });
    }

    /// Pushes a new parsing step that parses the next field or to build the concatenation.
    pub(crate) fn push_next_field<N: TinyParseImpl>(&mut self, expect: Expect, field: usize) {
        self.parsers.push(TinyParseFn {
            parse: N::tiny_parse_iterative,
            expect,
            field: field + 1,
            repetition: false,
        });
    }

    /// Pushes a new parsing step that parses the same field again.
    pub(crate) fn push_repetition<N: TinyParseImpl>(&mut self, expect: Expect, field: usize) {
        self.parsers.push(TinyParseFn {
            parse: N::tiny_parse_iterative,
            expect,
            field,
            repetition: true,
        });
    }
}

/// Implementation detail for [`TinyParse`].
pub(crate) trait TinyParseImpl: ParseImpl + Sized {
    /// Used by [`TinyParse::tiny_parse_fast()`].
    fn tiny_parse_nested(lexer: &mut CheckedTinyLexer, expect: Expect) -> TinyResult<Self>;

    /// Used by [`TinyParse::tiny_parse_safe()`].
    fn tiny_parse_iterative(
        state: &mut TinyParseState,
        expect: Expect,
        field: usize,
        repetition: bool,
    ) -> TinyResult<()>;

    /// Used at the very end to pop the last node from the node stack.
    fn pop_final_node(nodes: &mut NodeStack<Tiny>) -> Self;
}

/// Allows parsing both fast (recursively; might stack overflow) and safe (iteratively).
pub(crate) trait TinyParse: TinyParseImpl {
    /// Parses recursively.
    ///
    /// This is very fast, but might lead to a stack overflow for deeply nested code. To avoid
    /// crashes for e.g. untrusted input, use [`TinyParse::tiny_parse_safe()`].
    ///
    /// One could add a `max_recursion` limit here, but that can't really provide any guarantees,
    /// since the stack might already be almost full despite a low limit.
    ///
    /// Additionally, I would have to duplicate a bunch of code, since I don't want this recursion
    /// check to slow down parsing (even though it probably wouldn't be much). I might look into
    /// this again in the future, but for now I'll keep it as is.
    fn tiny_parse_fast(code: &str) -> TinyResult<Self> {
        let lexer = TinyLexer::new(code);
        let mut lexer = CheckedTinyLexer::new(lexer, Self::INITIAL_EXPECT)?;
        Self::tiny_parse_nested(&mut lexer, Expect::END_OF_INPUT)
    }

    /// Parses iteratively rather than recursively to avoid stack overflow.
    ///
    /// Keep in mind, that you might also want to limit the size of the input to some maximum to
    /// also effectively limit its execution time, so that it doesn't hang up the program.
    ///
    /// Furthermore, since tokens can be arbitrarily large, limit the actual input, not just the
    /// number of tokens.
    fn tiny_parse_safe(code: &str) -> TinyResult<Self> {
        let lexer = TinyLexer::new(code);
        let lexer = CheckedTinyLexer::new(lexer, Self::INITIAL_EXPECT)?;
        let mut state = TinyParseState::new(lexer);
        Self::tiny_parse_iterative(&mut state, Expect::END_OF_INPUT, 0, false)?;
        while let Some(parser) = state.parsers.pop() {
            parser.parse(&mut state)?;
        }
        assert!(state.tokens.finish(), "token stack should be empty");
        let result = Self::pop_final_node(&mut state.nodes);
        assert!(state.nodes.finish(), "node stack should be empty");
        Ok(result)
    }
}

impl<T: TinyParseImpl> TinyParse for T {}

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
    /// Creates an empty stack.
    fn new() -> Self {
        Self::default()
    }

    /// Consumes [`self`] and returns if the stack is empty, which should always be the case at the
    /// end of parsing.
    fn finish(self) -> bool {
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

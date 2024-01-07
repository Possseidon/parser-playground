use std::fmt;

use bitvec::vec::BitVec;
use enum_map::{Enum, EnumMap};
use paste::paste;
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::{
    lexer::{FatalLexerError, TinyLexer},
    push_array::PushArray,
    token::{token, Style, Tiny, TinyToken, Token, TokenKind, TokenSet},
};

enum ParseErrorKind {
    TokensExpectedFoundEndOfInput {
        expected: TokenSet,
    },
    TokensExpectedFoundToken {
        expected: TokenSet,
        found: TokenKind,
    },
}

struct ParseError {
    kind: ParseErrorKind,
    pos: usize,
    len: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NestedTokenSet {
    tokens: TokenSet,
    exhaustive: bool,
}

impl NestedTokenSet {
    pub(crate) const fn new() -> Self {
        Self {
            tokens: TokenSet::new(),
            exhaustive: true,
        }
    }

    pub(crate) const fn from_kind(kind: TokenKind) -> Self {
        Self {
            tokens: TokenSet::from_kind(kind),
            exhaustive: true,
        }
    }

    pub(crate) const fn xor_without_ambiguity_const(self, other: Self) -> Self {
        Self {
            tokens: self.tokens.xor_without_ambiguity_const(other.tokens),
            exhaustive: self.exhaustive && other.exhaustive,
        }
    }

    pub(crate) fn xor_without_ambiguity(self, other: Self) -> Self {
        Self {
            tokens: self.tokens.xor_without_ambiguity(other.tokens),
            exhaustive: self.exhaustive && other.exhaustive,
        }
    }

    pub(crate) const fn non_exhaustive(self) -> Self {
        Self {
            exhaustive: false,
            ..self
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TinyParseFn {
    parse: fn(
        lexer: &mut TinyLexer,
        state: &mut TinyParseState,
        expect: Expect,
        field: usize,
        repetition: bool,
    ) -> Result<(), FatalLexerError>,
    expect: Expect,
    field: usize,
    repetition: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct TinyParseState {
    parsers: Vec<TinyParseFn>,
    tokens: TinyTokenStack,
    nodes: NodeStack<Tiny>,
}

trait TinyParseImpl: Sized {
    /// Prepares the lexer for parsing and returns the trailing [`Expect`] of this type.
    ///
    /// "Prepare" means, it checks the first token, since new tokens are always checked immediately.
    fn tiny_prepare_lexer(lexer: &mut TinyLexer) -> Result<Expect, FatalLexerError>;

    /// Used by [`TinyParse::tiny_parse_fast()`].
    fn tiny_parse_nested(lexer: &mut TinyLexer, expect: Expect) -> Result<Self, FatalLexerError>;

    /// Used by [`TinyParse::tiny_parse_safe()`] and [`TinyParse::tiny_parse_with_depth()`].
    fn tiny_parse_iterative(
        lexer: &mut TinyLexer,
        state: &mut TinyParseState,
        expect: Expect,
        field: usize,
        repetition: bool,
    ) -> Result<(), FatalLexerError>;

    /// Used at the very end to last node from the node stack.
    fn pop_final_node(nodes: &mut NodeStack<Tiny>) -> Self;
}

#[allow(private_bounds)]
pub(crate) trait TinyParse: TinyParseImpl {
    /// Parses recursively.
    ///
    /// This is very fast, but might lead to a stack overflow for deeply nested code. To avoid
    /// crashes for e.g. untrusted input, use [`TinyParse::tiny_parse_safe()`] or better yet
    /// [`TinyParse::tiny_parse_with_depth()`] to also limit execution time.
    ///
    /// One could add a `max_recursion` limit here, similar to `max_depth` in
    /// [`TinyParse::tiny_parse_with_depth()`], but that can't really provide any guarantees, since
    /// the stack might already be almost full despite a low limit.
    ///
    /// Additionally, I would have to duplicate a bunch of code, since I don't want this recursion
    /// check to slow down parsing (even though it probably wouldn't be much). I might look into
    /// this again in the future, but for now I'll keep it as is.
    fn tiny_parse_fast(code: &str) -> Result<Self, FatalLexerError> {
        let mut lexer = TinyLexer::new(code)?;
        let expect = Self::tiny_prepare_lexer(&mut lexer)?;
        Self::tiny_parse_nested(&mut lexer, expect)
    }

    /// Parses iteratively to avoid stack overflow.
    ///
    /// While this is safe from crashes, it can still take a very long time for large inputs.
    /// To avoid even that, use [`TinyParse::tiny_parse_with_depth()`] and limit the depth to a
    /// reasonable value.
    ///
    /// Simply calls [`TinyParse::tiny_parse_with_depth()`] with a maximum depth of [`usize::MAX`].
    fn tiny_parse_safe(code: &str) -> Result<Self, FatalLexerError> {
        Self::tiny_parse_with_depth(code, usize::MAX)
    }

    /// Parses iteratively with a maximum depth to avoid long execution times.
    ///
    /// TODO: Return a different type of error when max_depth is exceeded.
    fn tiny_parse_with_depth(code: &str, max_depth: usize) -> Result<Self, FatalLexerError> {
        let mut lexer = TinyLexer::new(code)?;
        let mut state = TinyParseState::default();
        let expect = Self::tiny_prepare_lexer(&mut lexer)?;
        Self::tiny_parse_iterative(&mut lexer, &mut state, expect, 0, false)?;
        while let Some(TinyParseFn {
            parse,
            expect,
            field,
            repetition,
        }) = state.parsers.pop()
        {
            // TODO: check max_depth limit
            //       Separate limits for state.parsers/.tokens/.noces?
            //       Do I even have to check all or does one of them also limit the other ones in some way?
            parse(&mut lexer, &mut state, expect, field, repetition)?;
        }
        assert!(state.tokens.is_empty());
        let result = Self::pop_final_node(&mut state.nodes);
        assert!(state.nodes.is_empty());
        Ok(result)
    }
}

impl<T: TinyParseImpl> TinyParse for T {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Expect {
    tokens: TokenSet,
    or_end_of_input: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct TinyTokenStack {
    /// For every `true`, there is also an entry in [`Self::tokens`].
    ///
    /// When using marked push/pop operations, [`Self::dynamic`]'s entries are omitted when marked.
    dynamic: BitVec,
    /// Excludes empty strings, which are instead indicated as `false` in [Self::dynamic].
    tokens: Vec<SmolStr>,
    /// Pushed for optional elements.
    ///
    /// If and only if `true` is pushed, there is also a matching entry in [`Self::dynamic`].
    optional: BitVec,
    /// Contains the start index of a repetition in [`Self::dynamic`] and [`Self::tokens`].
    repetition: SmallVec<[[usize; 2]; 1]>,
}

impl TinyTokenStack {
    fn new() -> Self {
        Self::default()
    }

    /// Intentionally consumes self, signifying that this is the last operation.
    fn is_empty(self) -> bool {
        self.dynamic.is_empty() // && self.optional.is_empty() && self.repetition.is_empty()
    }

    fn push(&mut self, token: SmolStr) {
        if token.is_empty() {
            self.dynamic.push(false);
        } else {
            self.dynamic.push(true);
            self.tokens.push(token);
        }
    }

    fn pop(&mut self) -> SmolStr {
        if self
            .dynamic
            .pop()
            .expect("dynamic stack should not be empty")
        {
            self.tokens.pop().expect("token stack should not be empty")
        } else {
            SmolStr::new_inline("")
        }
    }

    fn push_some(&mut self, token: SmolStr) {
        self.optional.push(true);
        self.push(token);
    }

    /// Pushed either in place of a missing optional or at the start of a repetition.
    fn push_none(&mut self) {
        self.optional.push(false);
    }

    /// Pops a single optional token.
    fn pop_optional(&mut self) -> Option<SmolStr> {
        self.optional
            .pop()
            .expect("optional stack should not be empty")
            .then(|| self.pop())
    }

    /// Marks the start of a new repetition. Elements must be pushed using [`Self::push()`].
    fn start_repetition(&mut self) {
        self.repetition
            .push([self.dynamic.len(), self.tokens.len()]);
    }

    /// Pops an entire repetition, marked by an initial marker followed by marked tokens.
    fn pop_repetition(&mut self) -> impl ExactSizeIterator<Item = SmolStr> + '_ {
        let [dynamic_start, tokens_start] = self
            .repetition
            .pop()
            .expect("repetition stack should not be empty");
        let mut tokens = self.tokens.drain(tokens_start..);
        self.dynamic.drain(dynamic_start..).map(move |dynamic| {
            if dynamic {
                tokens
                    .next()
                    .expect("tokens stack should contain more tokens")
            } else {
                SmolStr::new_inline("")
            }
        })
    }
}

macro_rules! tiny_parse_push_parser {
    ( $Node:ident $state:ident $expect:tt ) => {
        $state.parsers.push(TinyParseFn {
            parse: $Node::tiny_parse_iterative,
            expect: $expect,
            field: 0,
            repetition: false,
        })
    };
}

macro_rules! impl_enum_parse {
    ( $Name:ident {
        $( Tokens: [ $( $Token:ident, )* ] )?
        $( Nodes: [ $( $Node:ident, )* ] )?
    } ) => { paste! {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub(crate) enum $Name<S: Style> {
            $( $( $Token(Token<token::$Token, S>), )* )?
            $( $( $Node($Node<S>), )* )?
        }

        impl<S: Style> $Name<S> {
            const EXPECTED_TOKENS: NestedTokenSet = {
                NestedTokenSet::new()
                    $( $( .xor_without_ambiguity_const(NestedTokenSet::from_kind(TokenKind::$Token)) )* )?
                    $( $( .xor_without_ambiguity_const($Node::<S>::EXPECTED_TOKENS) )* )?
            };
        }

        const _: NestedTokenSet = $Name::<Tiny>::EXPECTED_TOKENS;

        impl TinyParseImpl for $Name<Tiny> {
            fn tiny_prepare_lexer(lexer: &mut TinyLexer) -> Result<Expect, FatalLexerError> {
                check_expected!(lexer (Expect {
                    tokens: Self::EXPECTED_TOKENS.tokens,
                    or_end_of_input: !Self::EXPECTED_TOKENS.exhaustive,
                }));
                Ok(Expect {
                    tokens: TokenSet::new(),
                    or_end_of_input: true,
                })
            }

            fn tiny_parse_nested(lexer: &mut TinyLexer, expect: Expect) -> Result<Self, FatalLexerError> {
                let found = lexer.peek_expected();

                $( $( if found == TokenKind::$Token {
                    return Ok(Self::$Token(tiny_parse_token!($Token lexer expect)));
                } )* )?

                $( $( if $Node::<Tiny>::EXPECTED_TOKENS.tokens.contains(found) {
                    return Ok(Self::$Node(tiny_parse_node!($Node lexer expect)));
                } )* )?

                unreachable!("token should match one of the above cases");
            }

            fn tiny_parse_iterative(
                lexer: &mut TinyLexer,
                state: &mut TinyParseState,
                expect: Expect,
                field: usize,
                _repetition: bool,
            ) -> Result<(), FatalLexerError> {
                if field == 1 {
                    let node = match state.nodes.pop_kind() {
                        $( $( NodeKind::$Node => Self::$Node(NodeStack::<Tiny>::pop(&mut state.nodes.[<$Node:snake>])), )* )?
                        _ => unreachable!("node should match one of the above cases"),
                    };
                    state.nodes.[<$Name:snake>].push(node);
                    return Ok(());
                }

                let found = lexer.peek_expected();

                $( $( if found == TokenKind::$Token {
                    state.nodes.[<$Name:snake>].push(Self::$Token(tiny_parse_token!($Token lexer expect)));
                    return Ok(());
                } )* )?

                state.parsers.push(TinyParseFn {
                    parse: Self::tiny_parse_iterative,
                    expect,
                    field: 1,
                    repetition: false,
                });

                $( $( if $Node::<Tiny>::EXPECTED_TOKENS.tokens.contains(found) {
                    state.nodes.push_kind(NodeKind::$Node);
                    tiny_parse_push_parser!($Node state expect);
                    return Ok(());
                } )* )?

                unreachable!("token should match one of the above cases");
            }

            impl_pop_final_node!($Name);
        }

        impl<S: Style> $Name<S> {
            fn drain_into_dropped_nodes(&mut self, nodes: &mut DroppedNodes<S>) {
                match self {
                    $( $( Self::$Node(node) => node.drain_into_dropped_nodes(nodes), )* )?
                    _ => {}
                }
            }
        }
    } };
}

macro_rules! field_type {
    ( [$Token:ident] ) => { Token<token::$Token, S> };
    ( [$Token:ident?] ) => { Option<Token<token::$Token, S>> };
    // Could in theory optimized repetitions of fixed tokens, since those can be represented by
    // a single usize, whereas SmallVec and Vec are always 24 bytes; but since a series of the same
    // fixed token would make for a quite odd grammar, there is no need to overcomplicate this.
    ( [$Token:ident*] ) => { SmallVec<[Token<token::$Token, S>; 1]> };
    ( ($Node:ident) ) => { $Node<S> };
    // While maybe useful, forbidding Box for unconditional nodes prevents unparsable grammars.
    // However, I think, it is almost always better to box an optional node instead anyway.
    // ( ($Node:ident[]) ) => { Box<$Node<S>> };
    ( ($Node:ident?) ) => { Option<$Node<S>> };
    ( ($Node:ident[?]) ) => { Option<Box<$Node<S>>> };
    ( ($Node:ident*) ) => { SmallVec<[$Node<S>; 1]> };
    ( ($Node:ident[*]) ) => { Vec<$Node<S>> };
}

macro_rules! token {
    ( $tokens:ident $Token:ident ) => {
        let $tokens =
            $tokens.xor_without_ambiguity_const(NestedTokenSet::from_kind(TokenKind::$Token));
    };
}

macro_rules! node {
    ( $tokens:ident $Node:ident ) => {
        let $tokens = $tokens.xor_without_ambiguity_const($Node::<Tiny>::EXPECTED_TOKENS);
    };
}

/// Returns everything up to and including the first required node.
macro_rules! until_required {
    ( $tokens:ident ) => { $tokens.non_exhaustive() };
    ( $tokens:ident [$Token:ident] $( $rest:tt )* ) => { { token!($tokens $Token); $tokens } };
    ( $tokens:ident [$Token:ident?] $( $rest:tt)* ) => { { token!($tokens $Token); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident [$Token:ident*] $( $rest:tt )* ) => { { token!($tokens $Token); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident ($Node:ident) $( $rest:tt )* ) => { { node!($tokens $Node); $tokens } };
    ( $tokens:ident ($Node:ident?) $( $rest:tt )* ) => { { node!($tokens $Node); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident ($Node:ident[?]) $( $rest:tt )* ) => { { node!($tokens $Node); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident ($Node:ident*) $( $rest:tt )* ) => { { node!($tokens $Node); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident ($Node:ident[*]) $( $rest:tt )* ) => { { node!($tokens $Node); until_required!( $tokens $( $rest )* ) } };
}

/// Executes the given macro repeatedly, popping the first item on each step.
macro_rules! repeat_until_empty {
    ( $array:ident ) => { $array };
    ( $array:ident $first:tt $( $rest:tt )* ) => { {
        let array = $array.push({
            let tokens = NestedTokenSet::new();
            until_required!(tokens $first $( $rest )* )
        });
        repeat_until_empty!( array $( $rest )* )
    } };
}

macro_rules! expected_tokens {
    ( [ $Token:ident $( $mode:tt )? ] ) => {
        NestedTokenSet::from_kind(TokenKind::$Token)
    };
    ( ( $Node:ident $( $mode:tt )? ) ) => {
        $Node::<Tiny>::EXPECTED_TOKENS
    };
}

macro_rules! check_expected {
    ( $lexer:ident $expect:tt ) => {{
        let expect = $expect;
        if let Some(next_token) = $lexer.peek() {
            if !expect.tokens.contains(next_token) {
                return Err(FatalLexerError);
            }
        } else if !expect.or_end_of_input {
            return Err(FatalLexerError);
        }
    }};
}

macro_rules! tiny_parse_token {
    ( $Token:ident $lexer:ident $expect:tt ) => {{
        let token = $lexer.next_expected()?;
        check_expected!($lexer $expect);
        Token::<token::$Token, Tiny>::new(token)
    }};
}

macro_rules! tiny_parse_node {
    ( $Node:ident $lexer:ident $expect:tt ) => {
        $Node::<Tiny>::tiny_parse_nested($lexer, $expect)?
    };
}

macro_rules! tiny_parse_repetition {
    ( $tiny_parse_token_or_node:ident $Vec:ident $TokenOrNode:ident $lexer:ident $matches:tt $expect:tt ) => { {
        let mut result = $Vec::new();
        while $lexer.peek_matches($matches) {
            result.push($tiny_parse_token_or_node!($TokenOrNode $lexer $expect));
        }
        result
    } };
}

macro_rules! tiny_parse_by_mode {
    ( [$Token:ident] $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_token!($Token $lexer $expect)
    };
    ( ($Node:ident) $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_node!($Node $lexer $expect)
    };
    ( [$Token:ident?] $lexer:ident match $matches:tt $expect:tt ) => {
        if $lexer.peek_matches($matches) { Some(tiny_parse_token!($Token $lexer $expect)) } else { None }
    };
    ( ($Node:ident?) $lexer:ident match $matches:tt $expect:tt ) => {
        if $lexer.peek_matches($matches) { Some(tiny_parse_node!($Node $lexer $expect)) } else { None }
    };
    ( ($Node:ident[?]) $lexer:ident match $matches:tt $expect:tt ) => {
        if $lexer.peek_matches($matches) { Some(Box::new(tiny_parse_node!($Node $lexer $expect))) } else { None }
    };
    ( [$Token:ident*] $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_repetition!(tiny_parse_token SmallVec $Token $lexer $matches $expect)
    };
    ( ($Node:ident*) $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_repetition!(tiny_parse_node SmallVec $Node $lexer $matches $expect)
    };
    ( ($Node:ident[*]) $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_repetition!(tiny_parse_node Vec $Node $lexer $matches $expect)
    };
}

macro_rules! tiny_parse_node_repetition_iterative {
    ( $Node:ident $lexer:ident $state:ident $original_expect:ident $field:ident $repetition:ident $matches:tt $expect:tt ) => { paste! {
        if !$repetition {
            NodeStack::<Tiny>::start_repetition(&mut $state.nodes.repetition, &mut $state.nodes.[<$Node:snake>]);
        }
        if $lexer.peek_matches($matches) {
            $state.parsers.push(TinyParseFn {
                parse: Self::tiny_parse_iterative,
                expect: $original_expect,
                field: $field,
                repetition: true,
            });
            tiny_parse_push_parser!($Node $state $expect);
        }
    } };
}

macro_rules! tiny_parse_by_mode_iterative {
    ( [$Token:ident] $lexer:ident $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => { paste! {
        $state.tokens.push($lexer.next_expected()?);
        check_expected!($lexer $expect);
    } };
    ( ($Node:ident) $lexer:ident $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        tiny_parse_push_parser!($Node $state $expect);
    };
    ( [$Token:ident?] $lexer:ident $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => { paste! {
        if $lexer.peek_matches($matches) {
            $state.tokens.push_some($lexer.next_expected()?);
            check_expected!($lexer $expect);
        } else {
            $state.tokens.push_none();
        }
    } };
    ( ($Node:ident?) $lexer:ident $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        if $lexer.peek_matches($matches) {
            $state.nodes.push_some();
            tiny_parse_push_parser!($Node $state $expect);
        } else {
            $state.nodes.push_none();
        }
    };
    ( ($Node:ident[?]) $lexer:ident $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        if $lexer.peek_matches($matches) {
            $state.nodes.push_some();
            tiny_parse_push_parser!($Node $state $expect);
        } else {
            $state.nodes.push_none();
        }
    };
    ( [$Token:ident*] $lexer:ident $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => { paste! {
        // TODO: This snippet exists 3 times with slight variations, deduplicate it with a macro
        $state.tokens.start_repetition();
        while $lexer.peek_matches($matches) {
            $state.tokens.push($lexer.next_expected()?);
            check_expected!($lexer $expect);
        }
    } };
    ( ($Node:ident*) $lexer:ident $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        tiny_parse_node_repetition_iterative!($Node $lexer $state $original_expect $field $repetition $matches $expect)
    };
    ( ($Node:ident[*]) $lexer:ident $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        tiny_parse_node_repetition_iterative!($Node $lexer $state $original_expect $field $repetition $matches $expect)
    };
}

macro_rules! expect_field_by_nested_token_set {
    ( $nested_token_set:ident $expect:tt) => {
        if $nested_token_set.exhaustive {
            Expect {
                tokens: $nested_token_set.tokens,
                or_end_of_input: false,
            }
        } else {
            let expect = $expect;
            Expect {
                // TODO: Check this at compile time (pretty sure it should be possible)
                tokens: $nested_token_set
                    .tokens
                    .xor_without_ambiguity(expect.tokens),
                or_end_of_input: expect.or_end_of_input,
            }
        }
    };
}

macro_rules! expect_next_field {
    ( $Name:ident $field:ident $expect:ident ) => {
        paste! {
            if let Some(next_field) = [<$Name:snake>]::Field::[<$field:camel>].next() {
                let next_expected_tokens = Self::EXPECTED_TOKENS_FROM[next_field];
                expect_field_by_nested_token_set!(next_expected_tokens $expect)
            } else {
                $expect
            }
        }
    };
}

macro_rules! expect_same_field {
    ( $Name:ident $field:ident $expect:ident ) => { paste! { {
        let same_expected_tokens = Self::EXPECTED_TOKENS_FROM[[<$Name:snake>]::Field::[<$field:camel>]];
        expect_field_by_nested_token_set!(same_expected_tokens $expect)
    } } };
}

macro_rules! expect_field {
    ( [$Token:ident] $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( ($Node:ident) $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( [$Token:ident?] $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( ($Node:ident?) $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( ($Node:ident[?]) $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( [$Token:ident*] $Name:ident $field:ident $expect:ident ) => {
        expect_same_field!($Name $field $expect)
    };
    ( ($Node:ident*) $Name:ident $field:ident $expect:ident ) => {
        expect_same_field!($Name $field $expect)
    };
    ( ($Node:ident[*]) $Name:ident $field:ident $expect:ident ) => {
        expect_same_field!($Name $field $expect)
    };
}

macro_rules! tiny_parse_build_field {
    ( [$Token:ident] $state:ident ) => {
        Token::new($state.tokens.pop())
    };
    ( ($Node:ident) $state:ident ) => { paste! {
        NodeStack::<Tiny>::pop(&mut $state.nodes.[<$Node:snake>])
    } };
    ( [$Token:ident?] $state:ident ) => {
        $state.tokens.pop_optional().map(Token::new)
    };
    ( ($Node:ident?) $state:ident ) => { paste! {
        NodeStack::<Tiny>::pop_optional(&mut $state.nodes.optional, &mut $state.nodes.[<$Node:snake>])
    } };
    ( ($Node:ident[?]) $state:ident ) => { paste! {
        NodeStack::<Tiny>::pop_optional(&mut $state.nodes.optional, &mut $state.nodes.[<$Node:snake>]).map(Box::new)
    } };
    ( [$Token:ident*] $state:ident ) => {{
        SmallVec::from_iter($state.tokens.pop_repetition().map(Token::new))
    }};
    ( ($Node:ident*) $state:ident ) => { paste! {
        SmallVec::from_iter(NodeStack::<Tiny>::pop_repetition(&mut $state.nodes.repetition, &mut $state.nodes.[<$Node:snake>]))
    } };
    ( ($Node:ident[*]) $state:ident ) => { paste! {
        Vec::from_iter(NodeStack::<Tiny>::pop_repetition(&mut $state.nodes.repetition, &mut $state.nodes.[<$Node:snake>]))
    } };
}

macro_rules! impl_pop_final_node {
    ( $Name:ident ) => {
        paste! {
            fn pop_final_node(nodes: &mut NodeStack<Tiny>) -> Self {
                nodes.[<$Name:snake>].pop().expect("final node should exist")
            }
        }
    };
}

macro_rules! reverse {
    () => {};
    ( $first:tt $( $rest:tt )* ) => {
        reverse!( $( $rest )* ); $first
    };
}

macro_rules! drain_field_into_dropped_nodes {
    ( [$Token:ident] $nodes:ident $self:ident $field:ident ) => {};
    ( ($Node:ident) $nodes:ident $self:ident $field:ident ) => {};
    ( [$Token:ident?] $nodes:ident $self:ident $field:ident ) => {};
    ( ($Node:ident?) $nodes:ident $self:ident $field:ident ) => {};
    ( ($Node:ident[?]) $nodes:ident $self:ident $field:ident ) => {
        paste! {
            $nodes.[<$Node:snake>].extend($self.$field.take().map(|node| *node));
        }
    };
    ( [$Token:ident*] $nodes:ident $self:ident $field:ident ) => {};
    ( ($Node:ident*) $nodes:ident $self:ident $field:ident ) => {
        paste! {
            $nodes.[<$Node:snake>].extend($self.$field.drain(..));
        }
    };
    ( ($Node:ident[*]) $nodes:ident $self:ident $field:ident ) => {
        paste! {
            $nodes.[<$Node:snake>].extend($self.$field.drain(..));
        }
    };
}

macro_rules! impl_struct_parse {
    ( $Name:ident {
        $( $field:ident: $Field:tt, )*
    } ) => { paste! {
        mod [<$Name:snake>] {
            use enum_map::Enum;

            #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Enum)]
            pub(crate) enum Field {
                #[default]
                $( [<$field:camel>], )*
            }

            impl Field {
                pub(crate) fn next(self) -> Option<Self> {
                    let index = self.into_usize();
                    (index < Self::LENGTH - 1).then(|| Self::from_usize(index + 1))
                }
            }
        }

        pub(crate) struct $Name<S: Style> {
           $( $field: field_type!($Field), )*
        }

        impl<S: Style> Clone for $Name<S> {
            fn clone(&self) -> Self {
                Self {
                    $( $field: self.$field.clone(), )*
                }
            }
        }

        impl<S: Style> fmt::Debug for $Name<S> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct(stringify!($Name))
                    $( .field(stringify!($field), &self.$field) )*
                    .finish()
            }
        }

        impl<S: Style> PartialEq for $Name<S> {
            fn eq(&self, other: &Self) -> bool {
                $( self.$field == other.$field )&&*
            }
        }

        impl<S: Style> Eq for $Name<S> {}

        impl<S: Style> $Name<S> {
            /// Expected tokens for a given field only, even if it is not required.
            const EXPECTED_TOKENS_AT: EnumMap<[<$Name:snake>]::Field, TokenSet> = EnumMap::from_array([
                $( expected_tokens!($Field).tokens, )*
            ]);

            /// Expected tokens for a given field, including everything up until the first required field.
            const EXPECTED_TOKENS_FROM: EnumMap<[<$Name:snake>]::Field, NestedTokenSet> = EnumMap::from_array({
                let array = PushArray([]);
                repeat_until_empty!(array $( $Field )* ).0
            });

            /// Shorthand for the first entry in `EXPECTED_TOKENS_FROM`.
            ///
            /// Implemented in a way that does not introduce cycle compiler errors.
            const EXPECTED_TOKENS: NestedTokenSet = {
                let tokens = NestedTokenSet::new();
                until_required!(tokens $( $Field )* )
            };
        }

        const _: EnumMap<[<$Name:snake>]::Field, TokenSet> = $Name::<Tiny>::EXPECTED_TOKENS_AT;
        const _: EnumMap<[<$Name:snake>]::Field, NestedTokenSet> = $Name::<Tiny>::EXPECTED_TOKENS_FROM;
        const _: NestedTokenSet = $Name::<Tiny>::EXPECTED_TOKENS;

        impl TinyParseImpl for $Name<Tiny> {
            fn tiny_prepare_lexer(lexer: &mut TinyLexer) -> Result<Expect, FatalLexerError> {
                check_expected!(lexer (Expect {
                    tokens: Self::EXPECTED_TOKENS.tokens,
                    or_end_of_input: !Self::EXPECTED_TOKENS.exhaustive,
                }));
                Ok(Expect {
                    tokens: TokenSet::new(),
                    or_end_of_input: true,
                })
            }

            fn tiny_parse_nested(lexer: &mut TinyLexer, expect: Expect) -> Result<Self, FatalLexerError> {
                Ok(Self { $( $field: {
                    tiny_parse_by_mode!($Field lexer match {
                        Self::EXPECTED_TOKENS_AT[[<$Name:snake>]::Field::[<$field:camel>]]
                    } { expect_field!($Field $Name $field expect) })
                }, )* })
            }

            fn tiny_parse_iterative(
                lexer: &mut TinyLexer,
                state: &mut TinyParseState,
                expect: Expect,
                field: usize,
                repetition: bool,
            ) -> Result<(), FatalLexerError> {
                if field == [<$Name:snake>]::Field::LENGTH {
                    $( let $field; )*
                    reverse!( $( {
                        $field = tiny_parse_build_field!($Field state)
                    } )* );
                    state.nodes.[<$Name:snake>].push(Self { $( $field, )* });
                    return Ok(());
                }
                if !repetition {
                    state.parsers.push(TinyParseFn {
                        parse: Self::tiny_parse_iterative,
                        expect,
                        field: field + 1,
                        repetition: false,
                    });
                }
                match [<$Name:snake>]::Field::from_usize(field) { $( [<$Name:snake>]::Field::[<$field:camel>] => {
                    tiny_parse_by_mode_iterative!($Field lexer state expect field repetition match {
                        Self::EXPECTED_TOKENS_AT[[<$Name:snake>]::Field::[<$field:camel>]]
                    } { expect_field!($Field $Name $field expect) });
                } )* }
                Ok(())
            }

            impl_pop_final_node!($Name);
        }

        impl<S: Style> $Name<S> {
            fn drain_into_dropped_nodes(&mut self, nodes: &mut DroppedNodes<S>) {
                $( drain_field_into_dropped_nodes!($Field nodes self $field); )*
            }
        }

        impl<S: Style> Drop for $Name<S> {
            fn drop(&mut self) {
                let mut nodes = DroppedNodes::new();
                self.drain_into_dropped_nodes(&mut nodes);
            }
        }
    } };
}

macro_rules! impl_node_parse {
    ( $( $kind:ident $Name:ident $content:tt )* ) => { paste! {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        enum NodeKind {
            $( $Name, )*
        }

        type Kinds = SmallVec<[NodeKind; 16]>;
        const _: () = assert!(std::mem::size_of::<Kinds>() <= 24);

        type Repetition = SmallVec<[usize; 2]>;

        #[derive(Clone, Debug, PartialEq, Eq)]
        struct NodeStack<S: Style> {
            $( [<$Name:snake>]: Vec<$Name<S>>, )*
            kinds: Kinds,
            optional: BitVec,
            repetition: Repetition,
        }

        /// Used to avoid recursion on dropping of nodes.
        struct DroppedNodes<S: Style> {
            $( [<$Name:snake>]: Vec<$Name<S>>, )*
        }

        impl<S: Style> DroppedNodes<S> {
            fn new() -> Self {
                Self { $( [<$Name:snake>]: Vec::new(), )* }
            }
        }

        impl<S: Style> Drop for DroppedNodes<S> {
            fn drop(&mut self) {
                loop {
                    let mut empty = true;

                    $(
                        // must check empty before the loop, since a later field might push
                        empty &= self.[<$Name:snake>].is_empty();
                        while let Some(mut node) = self.[<$Name:snake>].pop() {
                            node.drain_into_dropped_nodes(self);
                        }
                    )*

                    if empty {
                        break;
                    }
                }
            }
        }

        impl<S: Style> Default for NodeStack<S> {
            fn default() -> Self {
                Self::new()
            }
        }

        impl<S: Style> NodeStack<S> {
            fn new() -> Self {
                Self {
                    $( [<$Name:snake>]: Vec::new(), )*
                    kinds: Kinds::new(),
                    optional: BitVec::new(),
                    repetition: SmallVec::new(),
                }
            }

            /// Intentionally consumes self, signifying that this is the last operation.
            fn is_empty(self) -> bool {
                $( self.[<$Name:snake>].is_empty() && )* self.optional.is_empty() && self.repetition.is_empty()
            }

            fn push_kind(&mut self, kind: NodeKind) {
                self.kinds.push(kind);
            }

            fn pop_kind(&mut self) -> NodeKind {
                self.kinds.pop().expect("kinds should not be empty")
            }

            fn push<T>(fields: &mut Vec<T>, node: T) {
                fields.push(node);
            }

            fn pop<T>(fields: &mut Vec<T>) -> T {
                fields.pop().expect("fields should not be empty")
            }

            fn push_some(&mut self) {
                self.optional.push(true);
            }

            fn push_none(&mut self) {
                self.optional.push(false);
            }

            fn pop_optional<T>(optional: &mut BitVec, fields: &mut Vec<T>) -> Option<T> {
                optional.pop().expect("optional should not be empty").then(|| Self::pop(fields))
            }

            fn start_repetition<T>(repetition: &mut Repetition, fields: &Vec<T>) {
                repetition.push(fields.len());
            }

            fn pop_repetition<'a, T>(repetition: &mut SmallVec<[usize; 2]>, fields: &'a mut Vec<T>) -> impl ExactSizeIterator<Item = T> + 'a {
                let start = repetition.pop().expect("repetitions should not be empty");
                fields.drain(start..)
            }
        }

        $( impl_node_parse!(#inner $kind $Name $content); )*
    } };
    ( #inner struct $Name:ident $content:tt ) => {
        impl_struct_parse!($Name $content);
    };
    ( #inner enum $Name:ident $content:tt ) => {
        impl_enum_parse!($Name $content);
    }
}

impl_node_parse! {
    enum UnaryOperator {
        Tokens: [
            Not,
            Minus,
        ]
    }

    enum BinaryOperator {
        Tokens: [
            Plus,
            // Minus,
            // Star,
            // Slash,
            // Percent,
            // Caret,
            // And,
            // Or,
            // AndAnd,
            // OrOr,
            // Shl,
            // Shr,
            // PlusEq,
            // MinusEq,
            // StarEq,
            // SlashEq,
            // PercentEq,
            // CaretEq,
            // AndEq,
            // OrEq,
            // ShlEq,
            // ShrEq,
            // EqEq,
            // Ne,
            // Gt,
            // Lt,
            // Ge,
            // Le,
        ]
    }

    enum Literal {
        Tokens: [
            Integer,
            Float,
            // String,
            // Char,
        ]
    }

    // TODO: Try to detect ambiguous grammer like the following:
    //       "+ +" is parsed as follows:
    //
    // SelfRepetition{
    //     plus: todo!(),
    //     more: vec![SelfRepetition{ plus: todo!(), more: vec![] }, ],
    // };
    //
    // Which is now ambiguous in which vec to push a theoretical new SelfRepetition into.
    struct SelfRepetition {
        plus: [Plus],
        more: (SelfRepetition[*]),
    }

    struct Other {
        a: [Ident*],
        b: [Fn?],
        c: [Plus],
    }

    struct StructNode {
        fn_kw: [Fn],
    }

    enum EnumNode {
        Tokens: [
            Struct,
            Mod,
        ]
        Nodes: [
            StructNode,
        ]
    }

    struct Test {
        token: [Ident],
        optional_token: [Integer?],
        token_repetition: [Float*],
        struct_node: (StructNode),
        sep1: [Comma],
        optional_struct_node: (StructNode?),
        sep2: [Comma],
        struct_node_repetition: (StructNode*),
        sep3: [Comma],
        enum_node: (EnumNode),
        sep4: [Comma],
        optional_enum_node: (EnumNode?),
        sep5: [Comma],
        enum_node_repetition: (EnumNode*),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        // TODO: Sort macros
        // TODO: Try running different parsers on strings generated by the Arbtirary crate.
        let result = Test::tiny_parse_safe(
            "hello 42 1.0 2.0 3.0 fn, fn, fn fn fn, struct, mod, fn struct mod",
        )
        .unwrap();
        println!("{result:#?}");
    }
}

use std::fmt;

use bitvec::vec::BitVec;
use enum_map::{Enum, EnumMap};
use paste::paste;
use smallvec::SmallVec;
use smol_str::SmolStr;

use crate::{
    lexer::{CheckedTinyTokenStream, FatalLexerError, IntoTinyTokenStream, TinyTokenStream},
    push_array::PushArray,
    token::{token, Expect, NestedTokenSet, Style, Tiny, TinyToken, Token, TokenKind, TokenSet},
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

#[derive(Clone, Copy, Debug)]
struct TinyParseFn<T: TinyTokenStream> {
    parse: fn(
        state: &mut TinyParseState<T>,
        expect: Expect,
        field: usize,
        repetition: bool,
    ) -> Result<(), FatalLexerError>,
    expect: Expect,
    field: usize,
    repetition: bool,
}

impl<T: TinyTokenStream> TinyParseFn<T> {
    fn parse(self, state: &mut TinyParseState<T>) -> Result<(), FatalLexerError> {
        (self.parse)(state, self.expect, self.field, self.repetition)
    }
}

#[derive(Debug)]
struct TinyParseState<T: TinyTokenStream> {
    token_stream: CheckedTinyTokenStream<T>,
    parsers: Vec<TinyParseFn<T>>,
    tokens: TinyTokenStack,
    nodes: NodeStack<Tiny>,
}

impl<T: TinyTokenStream> TinyParseState<T> {
    fn new(token_stream: CheckedTinyTokenStream<T>) -> Self {
        Self {
            token_stream,
            parsers: Vec::new(),
            tokens: TinyTokenStack::new(),
            nodes: NodeStack::new(),
        }
    }

    fn push_parser<N: TinyParseImpl>(&mut self, expect: Expect) {
        self.parsers.push(TinyParseFn {
            parse: N::tiny_parse_iterative,
            expect,
            field: 0,
            repetition: false,
        })
    }

    fn push_build_enum<N: TinyParseImpl>(&mut self, expect: Expect) {
        self.parsers.push(TinyParseFn {
            parse: N::tiny_parse_iterative,
            expect,
            field: 1,
            repetition: false,
        });
    }

    fn push_next_field<N: TinyParseImpl>(&mut self, expect: Expect, field: usize) {
        self.parsers.push(TinyParseFn {
            parse: N::tiny_parse_iterative,
            expect,
            field: field + 1,
            repetition: false,
        });
    }

    fn push_repetition<N: TinyParseImpl>(&mut self, expect: Expect, field: usize) {
        self.parsers.push(TinyParseFn {
            parse: N::tiny_parse_iterative,
            expect,
            field,
            repetition: true,
        });
    }
}

trait TinyParseImpl: Sized {
    /// Which tokens are initially expected.
    const EXPECTED_TOKENS: NestedTokenSet;

    const INITIAL_EXPECT: Expect = Expect {
        tokens: Self::EXPECTED_TOKENS.tokens,
        or_end_of_input: !Self::EXPECTED_TOKENS.exhaustive,
    };

    /// Used by [`TinyParse::tiny_parse_fast()`].
    fn tiny_parse_nested(
        token_stream: &mut CheckedTinyTokenStream<impl TinyTokenStream>,
        expect: Expect,
    ) -> Result<Self, FatalLexerError>;

    /// Used by [`TinyParse::tiny_parse_safe()`] and [`TinyParse::tiny_parse_with_depth()`].
    fn tiny_parse_iterative(
        state: &mut TinyParseState<impl TinyTokenStream>,
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
    fn tiny_parse_fast(token_stream: impl IntoTinyTokenStream) -> Result<Self, FatalLexerError> {
        let mut token_stream =
            CheckedTinyTokenStream::new(token_stream.into_iter(), Self::INITIAL_EXPECT)?;
        Self::tiny_parse_nested(&mut token_stream, Expect::END_OF_INPUT)
    }

    /// Parses iteratively to avoid stack overflow.
    ///
    /// While this is safe from crashes, it can still take a very long time for large inputs.
    /// To avoid even that, use [`TinyParse::tiny_parse_with_depth()`] and limit the depth to a
    /// reasonable value.
    ///
    /// Simply calls [`TinyParse::tiny_parse_with_depth()`] with a maximum depth of [`usize::MAX`].
    fn tiny_parse_safe(token_stream: impl IntoTinyTokenStream) -> Result<Self, FatalLexerError> {
        Self::tiny_parse_with_depth(token_stream, usize::MAX)
    }

    /// Parses iteratively with a maximum depth to avoid long execution times.
    fn tiny_parse_with_depth(
        token_stream: impl IntoTinyTokenStream,
        max_depth: usize,
    ) -> Result<Self, FatalLexerError> {
        let mut state = TinyParseState::new(CheckedTinyTokenStream::new(
            token_stream.into_iter(),
            Self::INITIAL_EXPECT,
        )?);
        Self::tiny_parse_iterative(&mut state, Expect::END_OF_INPUT, 0, false)?;
        while let Some(parse_fn) = state.parsers.pop() {
            parse_fn.parse(&mut state)?;
        }
        assert!(state.tokens.is_empty(), "leftover tokens after parsing");
        let result = Self::pop_final_node(&mut state.nodes);
        assert!(state.nodes.is_empty(), "leftover nodes after parsing");
        Ok(result)
    }
}

impl<T: TinyParseImpl> TinyParse for T {}

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
    /// Contains the start indices of a repetition in [`Self::dynamic`] and [`Self::tokens`].
    repetition: SmallVec<[[usize; 2]; 1]>,
}

impl TinyTokenStack {
    fn new() -> Self {
        Self::default()
    }

    /// Intentionally consumes self, signifying that this is the last operation.
    fn is_empty(self) -> bool {
        self.dynamic.is_empty() && self.optional.is_empty() && self.repetition.is_empty()
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

macro_rules! impl_enum_parse {
    ( $Name:ident {
        $( [$Token:ident], )*
        $( ($Node:ident), )*
    } ) => { paste! {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub(crate) enum $Name<S: Style> {
            $( $Token(Token<token::$Token, S>), )*
            $( $Node($Node<S>), )*
        }

        impl<S: Style> $Name<S> {
            const LAST_REQUIRED_AND_NON_EXHAUSTIVE_NODES: NodeSet = NodeSet {
                $( [<$Node:snake>]: true, )*
                ..NodeSet::new()
            };

            fn drain_into_dropped_nodes(&mut self, nodes: &mut DroppedNodes<S>) {
                match self {
                    $( Self::$Node(node) => node.drain_into_dropped_nodes(nodes), )*
                    _ => {}
                }
            }
        }

        const _: NestedTokenSet = $Name::<Tiny>::EXPECTED_TOKENS;

        impl TinyParseImpl for $Name<Tiny> {
            const EXPECTED_TOKENS: NestedTokenSet = {
                NestedTokenSet::new()
                    $( .xor_without_ambiguity_const(NestedTokenSet::from_kind(TokenKind::$Token)) )*
                    $( .xor_without_ambiguity_const($Node::<Tiny>::EXPECTED_TOKENS) )*
            };

            fn tiny_parse_nested(token_stream: &mut CheckedTinyTokenStream<impl TinyTokenStream>, expect: Expect) -> Result<Self, FatalLexerError> {
                let found = token_stream.kind();

                $( if found == TokenKind::$Token {
                    return Ok(Self::$Token(Token::<token::$Token, Tiny>::new(token_stream.next(expect)?)));
                } )*

                $( if $Node::<Tiny>::EXPECTED_TOKENS.tokens.contains(found) {
                    return Ok(Self::$Node($Node::<Tiny>::tiny_parse_nested(token_stream, expect)?));
                } )*

                unreachable!("token should match one of the above cases");
            }

            fn tiny_parse_iterative(
                state: &mut TinyParseState<impl TinyTokenStream>,
                expect: Expect,
                field: usize,
                _repetition: bool,
            ) -> Result<(), FatalLexerError> {
                if field == 1 {
                    let node = match state.nodes.pop_kind() {
                        $( NodeKind::$Node => Self::$Node(NodeStack::<Tiny>::pop(&mut state.nodes.[<$Node:snake>])), )*
                        _ => unreachable!("node should match one of the above cases"),
                    };
                    state.nodes.[<$Name:snake>].push(node);
                    return Ok(());
                }

                let found = state.token_stream.kind();

                $( if found == TokenKind::$Token {
                    state.nodes.[<$Name:snake>].push(Self::$Token(Token::<token::$Token, Tiny>::new(state.token_stream.next(expect)?)));
                    return Ok(());
                } )*

                state.push_build_enum::<Self>(expect);

                $( if $Node::<Tiny>::EXPECTED_TOKENS.tokens.contains(found) {
                    state.nodes.push_kind(NodeKind::$Node);
                    state.push_parser::<$Node<Tiny>>(expect);
                    return Ok(());
                } )*

                unreachable!("token should match one of the above cases");
            }

            impl_pop_final_node!($Name);
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

macro_rules! tiny_parse_token {
    ( $Token:ident $token_stream:ident $expect:tt ) => {{
        Token::<token::$Token, Tiny>::new($token_stream.next($expect)?)
    }};
}

macro_rules! tiny_parse_node {
    ( $Node:ident $token_stream:ident $expect:tt ) => {
        $Node::<Tiny>::tiny_parse_nested($token_stream, $expect)?
    };
}

macro_rules! tiny_parse_repetition {
    ( $tiny_parse_token_or_node:ident $Vec:ident $TokenOrNode:ident $token_stream:ident $matches:tt $expect:tt ) => { {
        let mut result = $Vec::new();
        while $token_stream.matches($matches) {
            result.push($tiny_parse_token_or_node!($TokenOrNode $token_stream $expect));
        }
        result
    } };
}

macro_rules! tiny_parse_by_mode {
    ( [$Token:ident] $token_stream:ident match $matches:tt $expect:tt ) => {
        tiny_parse_token!($Token $token_stream $expect)
    };
    ( ($Node:ident) $token_stream:ident match $matches:tt $expect:tt ) => {
        tiny_parse_node!($Node $token_stream $expect)
    };
    ( [$Token:ident?] $token_stream:ident match $matches:tt $expect:tt ) => {
        if $token_stream.matches($matches) { Some(tiny_parse_token!($Token $token_stream $expect)) } else { None }
    };
    ( ($Node:ident?) $token_stream:ident match $matches:tt $expect:tt ) => {
        if $token_stream.matches($matches) { Some(tiny_parse_node!($Node $token_stream $expect)) } else { None }
    };
    ( ($Node:ident[?]) $token_stream:ident match $matches:tt $expect:tt ) => {
        if $token_stream.matches($matches) { Some(Box::new(tiny_parse_node!($Node $token_stream $expect))) } else { None }
    };
    ( [$Token:ident*] $token_stream:ident match $matches:tt $expect:tt ) => {
        tiny_parse_repetition!(tiny_parse_token SmallVec $Token $token_stream $matches $expect)
    };
    ( ($Node:ident*) $token_stream:ident match $matches:tt $expect:tt ) => {
        tiny_parse_repetition!(tiny_parse_node SmallVec $Node $token_stream $matches $expect)
    };
    ( ($Node:ident[*]) $token_stream:ident match $matches:tt $expect:tt ) => {
        tiny_parse_repetition!(tiny_parse_node Vec $Node $token_stream $matches $expect)
    };
}

macro_rules! tiny_parse_node_repetition_iterative {
    ( $Node:ident $state:ident $original_expect:ident $field:ident $repetition:ident $matches:tt $expect:tt ) => { paste! {
        if !$repetition {
            NodeStack::<Tiny>::start_repetition(&mut $state.nodes._repetition, &mut $state.nodes.[<$Node:snake>]);
        }
        if $state.token_stream.matches($matches) {
            $state.push_repetition::<Self>($original_expect, $field);
            $state.push_parser::<$Node<Tiny>>($expect);
        }
    } };
}

macro_rules! tiny_parse_by_mode_iterative {
    ( [$Token:ident] $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => { paste! {
        $state.tokens.push($state.token_stream.next($expect)?);
    } };
    ( ($Node:ident) $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        $state.push_parser::<$Node<Tiny>>($expect);
    };
    ( [$Token:ident?] $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => { paste! {
        if $state.token_stream.matches($matches) {
            $state.tokens.push_some($state.token_stream.next($expect)?);
        } else {
            $state.tokens.push_none();
        }
    } };
    ( ($Node:ident?) $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        if $state.token_stream.matches($matches) {
            $state.nodes.push_some();
            $state.push_parser::<$Node<Tiny>>($expect);
        } else {
            $state.nodes.push_none();
        }
    };
    ( ($Node:ident[?]) $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        if $state.token_stream.matches($matches) {
            $state.nodes.push_some();
            $state.push_parser::<$Node<Tiny>>($expect);
        } else {
            $state.nodes.push_none();
        }
    };
    ( [$Token:ident*] $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => { paste! {
        $state.tokens.start_repetition();
        while $state.token_stream.matches($matches) {
            $state.tokens.push($state.token_stream.next($expect)?);
        }
    } };
    ( ($Node:ident*) $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        tiny_parse_node_repetition_iterative!($Node $state $original_expect $field $repetition $matches $expect)
    };
    ( ($Node:ident[*]) $state:ident $original_expect:ident $field:ident $repetition:ident match $matches:tt $expect:tt ) => {
        tiny_parse_node_repetition_iterative!($Node $state $original_expect $field $repetition $matches $expect)
    };
}

macro_rules! expect_next_field {
    ( $Name:ident $field:ident $expect:ident ) => {
        paste! {
            if let Some(next_field) = [<$Name:snake>]::Field::[<$field:camel>].next() {
                let next_expected_tokens = Self::EXPECTED_TOKENS_FROM[next_field];
                next_expected_tokens.expect($expect)
            } else {
                $expect
            }
        }
    };
}

macro_rules! expect_same_field {
    ( $Name:ident $field:ident $expect:ident ) => { paste! { {
        let same_expected_tokens = Self::EXPECTED_TOKENS_FROM[[<$Name:snake>]::Field::[<$field:camel>]];
        same_expected_tokens.expect($expect)
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
        NodeStack::<Tiny>::pop_optional(&mut $state.nodes._optional, &mut $state.nodes.[<$Node:snake>])
    } };
    ( ($Node:ident[?]) $state:ident ) => { paste! {
        NodeStack::<Tiny>::pop_optional(&mut $state.nodes._optional, &mut $state.nodes.[<$Node:snake>]).map(Box::new)
    } };
    ( [$Token:ident*] $state:ident ) => {{
        SmallVec::from_iter($state.tokens.pop_repetition().map(Token::new))
    }};
    ( ($Node:ident*) $state:ident ) => { paste! {
        SmallVec::from_iter(NodeStack::<Tiny>::pop_repetition(&mut $state.nodes._repetition, &mut $state.nodes.[<$Node:snake>]))
    } };
    ( ($Node:ident[*]) $state:ident ) => { paste! {
        Vec::from_iter(NodeStack::<Tiny>::pop_repetition(&mut $state.nodes._repetition, &mut $state.nodes.[<$Node:snake>]))
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
    ( ($Node:ident) $nodes:ident $self:ident $field:ident ) => {
        paste! {
            $self.$field.drain_into_dropped_nodes($nodes);
        }
    };
    ( [$Token:ident?] $nodes:ident $self:ident $field:ident ) => {};
    ( ($Node:ident?) $nodes:ident $self:ident $field:ident ) => {
        paste! {
            $self.$field.as_mut().map(|node| node.drain_into_dropped_nodes($nodes));
        }
    };
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

macro_rules! ensure_no_recursive_node_repetition_impl {
    ( $Name:ident $Field:ident $field:ident ) => { paste! {
        if !$Name::<Tiny>::EXPECTED_TOKENS_FROM.as_array()[[<$Name:snake>]::Field::[<$field:camel>] as usize].exhaustive  {
            let mut banned_nodes = NodeSet::new();
            banned_nodes.[<$Name:snake>] = true;
            let mut start_nodes = NodeSet::new();
            start_nodes.[<$Field:snake>] = true;
            if start_nodes.any_recursive_node(banned_nodes, NodeSet::new()) {
                panic!(concat!("non-exhaustive repetition ", stringify!($Name), "::", stringify!($field), " causes ambiguity due to cycle"));
            }
        }
    } };
}

macro_rules! ensure_no_recursive_node_repetition {
    ( $Name:ident ($Field:ident*) $field:ident ) => {
        ensure_no_recursive_node_repetition_impl!($Name $Field $field)
    };
    ( $Name:ident ($Field:ident[*]) $field:ident ) => {
        ensure_no_recursive_node_repetition_impl!($Name $Field $field)
    };
    ( $Name:ident $Field:tt $field:ident ) => {};
}

macro_rules! if_node {
    ( ($Node:ident $( $kind:tt )? ) $stmt:tt ) => {
        $stmt
    };
    ( [$Token:ident $( $kind:tt )? ] $stmt:tt ) => {};
}

macro_rules! nodes_dot_field {
    ( $nodes:ident ($Field:ident $( $kind:tt )? ) ) => {
        paste! {
            $nodes.[<$Field:snake>]
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

            const LAST_REQUIRED_AND_NON_EXHAUSTIVE_NODES: NodeSet = {
                let mut nodes = NodeSet::new();
                $( if_node!($Field {
                    let index = [<$Name:snake>]::Field::[<$field:camel>] as usize;
                    let is_non_exhaustive = !Self::EXPECTED_TOKENS_FROM.as_array()[index].exhaustive;
                    let is_last_required = index + 1 == [<$Name:snake>]::Field::LENGTH || !Self::EXPECTED_TOKENS_FROM.as_array()[index + 1].exhaustive;
                    nodes_dot_field!(nodes $Field) |= is_non_exhaustive || is_last_required;
                }); )*
                nodes
            };

            fn drain_into_dropped_nodes(&mut self, nodes: &mut DroppedNodes<S>) {
                $( drain_field_into_dropped_nodes!($Field nodes self $field); )*
            }
        }

        const _: EnumMap<[<$Name:snake>]::Field, TokenSet> = $Name::<Tiny>::EXPECTED_TOKENS_AT;
        const _: EnumMap<[<$Name:snake>]::Field, NestedTokenSet> = $Name::<Tiny>::EXPECTED_TOKENS_FROM;
        const _: NestedTokenSet = $Name::<Tiny>::EXPECTED_TOKENS;
        const _: () = { $( ensure_no_recursive_node_repetition!($Name $Field $field); )* };

        impl TinyParseImpl for $Name<Tiny> {
            /// Shorthand for the first entry in `EXPECTED_TOKENS_FROM`.
            ///
            /// Implemented in a way that does not introduce cycle compiler errors.
            const EXPECTED_TOKENS: NestedTokenSet = {
                let tokens = NestedTokenSet::new();
                until_required!(tokens $( $Field )* )
            };

            fn tiny_parse_nested(token_stream: &mut CheckedTinyTokenStream<impl TinyTokenStream>, expect: Expect) -> Result<Self, FatalLexerError> {
                Ok(Self { $( $field: {
                    tiny_parse_by_mode!($Field token_stream match {
                        Self::EXPECTED_TOKENS_AT[[<$Name:snake>]::Field::[<$field:camel>]]
                    } { expect_field!($Field $Name $field expect) })
                }, )* })
            }

            fn tiny_parse_iterative(
                state: &mut TinyParseState<impl TinyTokenStream>,
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
                    state.push_next_field::<Self>(expect, field);
                }
                match [<$Name:snake>]::Field::from_usize(field) { $( [<$Name:snake>]::Field::[<$field:camel>] => {
                    tiny_parse_by_mode_iterative!($Field state expect field repetition match {
                        Self::EXPECTED_TOKENS_AT[[<$Name:snake>]::Field::[<$field:camel>]]
                    } { expect_field!($Field $Name $field expect) });
                } )* }
                Ok(())
            }

            impl_pop_final_node!($Name);
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
            _kinds: Kinds,
            _optional: BitVec,
            _repetition: Repetition,
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
                    _kinds: Kinds::new(),
                    _optional: BitVec::new(),
                    _repetition: SmallVec::new(),
                }
            }

            /// Intentionally consumes self, signifying that this is the last operation.
            fn is_empty(self) -> bool {
                self._optional.is_empty()
                    && self._repetition.is_empty()
                    && $( self.[<$Name:snake>].is_empty() )&&*
            }

            fn push_kind(&mut self, kind: NodeKind) {
                self._kinds.push(kind);
            }

            fn pop_kind(&mut self) -> NodeKind {
                self._kinds.pop().expect("kinds should not be empty")
            }

            fn push<T>(fields: &mut Vec<T>, node: T) {
                fields.push(node);
            }

            fn pop<T>(fields: &mut Vec<T>) -> T {
                fields.pop().expect("fields should not be empty")
            }

            fn push_some(&mut self) {
                self._optional.push(true);
            }

            fn push_none(&mut self) {
                self._optional.push(false);
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

        #[derive(Clone, Copy, Debug)]
        struct NodeSet {
            $( [<$Name:snake>]: bool, )*
        }

        impl NodeSet {
            const fn new() -> Self {
                Self {
                    $( [<$Name:snake>]: false, )*
                }
            }

            const fn is_empty(self) -> bool {
                true
                    $( && !self.[<$Name:snake>] )*
            }

            const fn any_recursive_node(self, banned_node: NodeSet, mut checked_nodes: NodeSet) -> bool {
                if self.contains_any(banned_node) {
                    return true;
                }
                checked_nodes = checked_nodes.add(self);

                let mut recursive_nodes = Self::new();

                $( if self.[<$Name:snake>] {
                    recursive_nodes = recursive_nodes.add($Name::<Tiny>::LAST_REQUIRED_AND_NON_EXHAUSTIVE_NODES);
                } )*

                recursive_nodes = recursive_nodes.remove(checked_nodes);
                !recursive_nodes.is_empty() && recursive_nodes.any_recursive_node(banned_node, checked_nodes)
            }

            const fn add(self, nodes: NodeSet) -> Self {
                Self {
                    $( [<$Name:snake>]: self.[<$Name:snake>] || nodes.[<$Name:snake>], )*
                }
            }
            const fn remove(self, nodes: NodeSet) -> Self {
                Self {
                    $( [<$Name:snake>]: self.[<$Name:snake>] && !nodes.[<$Name:snake>], )*
                }
            }

            const fn contains_any(self, nodes: NodeSet) -> bool {
                $( self.[<$Name:snake>] && nodes.[<$Name:snake>] )||*
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
    [Not],
    [Minus],
}

enum BinaryOperator {
    [Plus],
    [Minus],
    [Star],
    [Slash],
    [Percent],
    [Caret],
    [And],
    [Or],
    [AndAnd],
    [OrOr],
    [Shl],
    [Shr],
    [PlusEq],
    [MinusEq],
    [StarEq],
    [SlashEq],
    [PercentEq],
    [CaretEq],
    [AndEq],
    [OrEq],
    [ShlEq],
    [ShrEq],
    [EqEq],
    [Ne],
    [Gt],
    [Lt],
    [Ge],
    [Le],
}

enum Literal {
    [Integer],
    [Float],
    [String],
    [Char],
}

struct SelfRepetition {
    l_paren: [LParen],
    more: (SelfRepetition[*]),
    r_paren: [RParen],
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
    [Struct],
    [Mod],
    (StructNode),
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

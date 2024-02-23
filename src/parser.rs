use std::{fmt, ops::Range};

use bitvec::vec::BitVec;
use enum_map::{Enum, EnumMap};
use paste::paste;
use smallvec::SmallVec;

use crate::{
    lexer::{CheckedLexer, Lexer, LexerError},
    push_array::PushArray,
    token::{
        tokens, Expect, NestedTokenSet, Style, Tiny, TokenKind, TokenStack, TokenStorage,
        TryCodeSpan,
    },
};

/// The state of an iterative parsing process.
///
/// Consists of a lexer and stacks for parsing steps, tokens and nodes.
#[derive(Debug)]
pub(crate) struct ParseState<'code, S: Style> {
    parsers: Vec<ParseStep<S>>,
    pub(crate) lexer: CheckedLexer<'code>,
    pub(crate) tokens: TokenStack,
    pub(crate) nodes: NodeStack<S>,
}

impl<'code, S: Style> ParseState<'code, S> {
    /// Creates a new parsing state from a lexer.
    pub(crate) fn new(lexer: CheckedLexer<'code>) -> Self {
        Self {
            parsers: Vec::new(),
            lexer,
            tokens: Default::default(),
            nodes: NodeStack::new(),
        }
    }

    /// Pushes a new parsing step for a normal node.
    pub(crate) fn push_parser<N: ParseImpl<S>>(&mut self, expect: Expect) {
        self.parsers.push(ParseStep {
            parse: N::parse_iterative,
            expect,
            field: 0,
            repetition: false,
        })
    }

    /// Pushes a new parsing step for building an alternation.
    pub(crate) fn push_build_enum<N: ParseImpl<S>>(&mut self, expect: Expect) {
        self.parsers.push(ParseStep {
            parse: N::parse_iterative,
            expect,
            field: 1,
            repetition: false,
        });
    }

    /// Pushes a new parsing step that parses the next field or to build the concatenation.
    pub(crate) fn push_next_field<N: ParseImpl<S>>(&mut self, expect: Expect, field: usize) {
        self.parsers.push(ParseStep {
            parse: N::parse_iterative,
            expect,
            field: field + 1,
            repetition: false,
        });
    }

    /// Pushes a new parsing step that parses the same field again.
    pub(crate) fn push_repetition<N: ParseImpl<S>>(&mut self, expect: Expect, field: usize) {
        self.parsers.push(ParseStep {
            parse: N::parse_iterative,
            expect,
            field,
            repetition: true,
        });
    }
}

type ParseFn<S> = fn(
    state: &mut ParseState<S>,
    expect: Expect,
    field: usize,
    repetition: bool,
) -> Result<(), LexerError>;

/// A single iterative parsing step.
#[derive(Clone, Copy, Debug)]
struct ParseStep<S: Style> {
    parse: ParseFn<S>,
    expect: Expect,
    field: usize,
    repetition: bool,
}

impl<S: Style> ParseStep<S> {
    /// Calls the `parse` function.
    fn parse(self, state: &mut ParseState<S>) -> Result<(), LexerError> {
        (self.parse)(state, self.expect, self.field, self.repetition)
    }
}

pub(crate) trait ExpectedTokens {
    /// Which tokens are initially expected as a [`NestedTokenSet`].
    const EXPECTED_TOKENS: NestedTokenSet;

    /// Which tokens are initially expected as an [`Expect`].
    const INITIAL_EXPECT: Expect = Expect {
        tokens: Self::EXPECTED_TOKENS.tokens,
        or_end_of_input: !Self::EXPECTED_TOKENS.exhaustive,
    };
}

pub(crate) trait ParseImpl<S: Style>: Sized + ExpectedTokens {
    /// Used by [`TinyParse::tiny_parse_safe()`] and [`PositionedParse::positioned_parse()`].
    fn parse_iterative(
        state: &mut ParseState<S>,
        expect: Expect,
        field: usize,
        repetition: bool,
    ) -> Result<(), LexerError>;

    /// Used at the very end to pop the last node from the node stack.
    fn pop_final_node(nodes: &mut NodeStack<S>) -> Self;

    /// Used by [`TinyParse::tiny_parse_fast()`].
    fn parse_nested(lexer: &mut CheckedLexer, expect: Expect) -> Result<Self, LexerError>;
}

pub(crate) trait Parse<S: Style>: ParseImpl<S> {
    /// Parses iteratively rather than recursively to avoid stack overflow.
    ///
    /// See [`ParseFast::parse_fast()`](crate::tiny::parser::ParseFast::parse_fast) for recursive
    /// parsing.
    ///
    /// Keep in mind, that you might also want to limit the size of the input to some maximum to
    /// also effectively limit its execution time, so that it doesn't hang up the program.
    fn parse(code: &str) -> Result<Self, LexerError> {
        let lexer = Lexer::new(code)?;
        let lexer = CheckedLexer::new(lexer, Self::INITIAL_EXPECT)?;
        let mut state = ParseState::<S>::new(lexer);
        Self::parse_iterative(&mut state, Expect::END_OF_INPUT, 0, false)?;
        while let Some(parser) = state.parsers.pop() {
            parser.parse(&mut state)?;
        }
        assert!(state.tokens.finish(), "token stack should be empty");
        let result = Self::pop_final_node(&mut state.nodes);
        assert!(state.nodes.finish(), "node stack should be empty");
        Ok(result)
    }

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
    fn parse_fast(code: &str) -> Result<Self, LexerError> {
        let lexer = Lexer::new(code)?;
        let mut lexer = CheckedLexer::new(lexer, Self::INITIAL_EXPECT)?;
        Self::parse_nested(&mut lexer, Expect::END_OF_INPUT)
    }
}

impl<S: Style, T: ParseImpl<S>> Parse<S> for T {}

/// Recursively parses a node.
macro_rules! parse_node {
    ( $Node:ident $lexer:ident $expect:tt ) => {
        $Node::<S>::parse_nested($lexer, $expect)?
    };
}

/// Recursively parses a repetition of nodes.
macro_rules! parse_node_repetition {
    ( $Vec:ident $Node:ident $lexer:ident $expect:tt ) => { {
        let mut result = $Vec::new();
        while $lexer.matches($Node::<S>::EXPECTED_TOKENS.tokens) {
            result.push(parse_node!($Node $lexer $expect));
        }
        result
    } };
}

/// Recursively parses a single field of a concatenation.
macro_rules! parse_by_mode {
    ( [$Token:ident] $lexer:ident $expect:tt ) => {
        tokens::$Token::parse_required::<S>($lexer, $expect)?
    };
    ( [$Token:ident?] $lexer:ident $expect:tt ) => {
        tokens::$Token::parse_optional::<S>($lexer, $expect)?
    };
    ( [$Token:ident*] $lexer:ident $expect:tt ) => {
        tokens::$Token::parse_repetition::<S>($lexer, $expect)?
    };
    ( ($Node:ident) $lexer:ident $expect:tt ) => {
        parse_node!($Node $lexer $expect)
    };
    ( ($Node:ident[]) $lexer:ident $expect:tt ) => {
        Box::new(parse_node!($Node $lexer $expect))
    };
    ( ($Node:ident?) $lexer:ident $expect:tt ) => {
        if $lexer.matches($Node::<S>::EXPECTED_TOKENS.tokens) { Some(parse_node!($Node $lexer $expect)) } else { None }
    };
    ( ($Node:ident[?]) $lexer:ident $expect:tt ) => {
        if $lexer.matches($Node::<S>::EXPECTED_TOKENS.tokens) { Some(Box::new(parse_node!($Node $lexer $expect))) } else { None }
    };
    ( ($Node:ident*) $lexer:ident $expect:tt ) => {
        parse_node_repetition!(SmallVec $Node $lexer $expect)
    };
    ( ($Node:ident[*]) $lexer:ident $expect:tt ) => {
        parse_node_repetition!(Vec $Node $lexer $expect)
    };
}

/// Iteratively parses a repetition of tokens or nodes.
macro_rules! parse_node_repetition_iterative {
    ( $Node:ident $state:ident $original_expect:ident $field:ident $repetition:ident $expect:tt ) => { paste! {
        if !$repetition {
            NodeStack::<S>::start_repetition(&mut $state.nodes._repetition, &mut $state.nodes.[<$Node:snake>]);
        }
        if $state.lexer.matches($Node::<S>::EXPECTED_TOKENS.tokens) {
            $state.push_repetition::<Self>($original_expect, $field);
            $state.push_parser::<$Node<S>>($expect);
        }
    } };
}

/// Iteratively parses a single field of a concatenation.
macro_rules! parse_by_mode_iterative {
    ( [$Token:ident] $state:ident $original_expect:ident $field:ident $repetition:ident $expect:tt ) => { paste! {
        tokens::$Token::push_required($state, $expect)?;
    } };
    ( [$Token:ident?] $state:ident $original_expect:ident $field:ident $repetition:ident $expect:tt ) => { paste! {
        tokens::$Token::push_optional($state, $expect)?;
    } };
    ( [$Token:ident*] $state:ident $original_expect:ident $field:ident $repetition:ident $expect:tt ) => { paste! {
        tokens::$Token::push_repetition($state, $expect)?;
    } };
    ( ($Node:ident $( [] )? ) $state:ident $original_expect:ident $field:ident $repetition:ident $expect:tt ) => {
        $state.push_parser::<$Node<S>>($expect);
    };
    ( ($Node:ident?) $state:ident $original_expect:ident $field:ident $repetition:ident $expect:tt ) => {
        if $state.lexer.matches($Node::<S>::EXPECTED_TOKENS.tokens) {
            $state.nodes.push_some();
            $state.push_parser::<$Node<S>>($expect);
        } else {
            $state.nodes.push_none();
        }
    };
    ( ($Node:ident[?]) $state:ident $original_expect:ident $field:ident $repetition:ident $expect:tt ) => {
        if $state.lexer.matches($Node::<S>::EXPECTED_TOKENS.tokens) {
            $state.nodes.push_some();
            $state.push_parser::<$Node<S>>($expect);
        } else {
            $state.nodes.push_none();
        }
    };
    ( ($Node:ident*) $state:ident $original_expect:ident $field:ident $repetition:ident $expect:tt ) => {
        parse_node_repetition_iterative!($Node $state $original_expect $field $repetition $expect)
    };
    ( ($Node:ident[*]) $state:ident $original_expect:ident $field:ident $repetition:ident $expect:tt ) => {
        parse_node_repetition_iterative!($Node $state $original_expect $field $repetition $expect)
    };
}

/// Next [`Expect`] after the given field.
///
/// Also takes in an outer [`Expect`] that is used for non-exhaustive fields.
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

/// The same [`Expect`] from the given field, used for repetitions.
///
/// Also takes in an outer [`Expect`] that is used for non-exhaustive fields.
macro_rules! expect_same_field {
    ( $Name:ident $field:ident $expect:ident ) => { paste! { {
        let same_expected_tokens = Self::EXPECTED_TOKENS_FROM[[<$Name:snake>]::Field::[<$field:camel>]];
        same_expected_tokens.expect($expect)
    } } };
}

/// What to expect after the given field.
///
/// For repetitions, this also includes the same field again, since it might repeat.
macro_rules! expect_field {
    ( [$Token:ident] $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( [$Token:ident?] $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( [$Token:ident*] $Name:ident $field:ident $expect:ident ) => {
        expect_same_field!($Name $field $expect)
    };
    ( ($Node:ident $( [] )? ) $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( ($Node:ident?) $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( ($Node:ident[?]) $Name:ident $field:ident $expect:ident ) => {
        expect_next_field!($Name $field $expect)
    };
    ( ($Node:ident*) $Name:ident $field:ident $expect:ident ) => {
        expect_same_field!($Name $field $expect)
    };
    ( ($Node:ident[*]) $Name:ident $field:ident $expect:ident ) => {
        expect_same_field!($Name $field $expect)
    };
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

/// Xors the given token into the given token set.
macro_rules! xor_token {
    ( $tokens:ident $Token:ident ) => {
        let $tokens =
            $tokens.xor_without_ambiguity_const(NestedTokenSet::from_kind(TokenKind::$Token));
    };
}

/// Xors the expected tokens of the given node into the given token set.
macro_rules! xor_node {
    ( $tokens:ident $Node:ident ) => {
        let $tokens = $tokens.xor_without_ambiguity_const($Node::<S>::EXPECTED_TOKENS);
    };
}

/// Returns everything up to and including the first required node.
macro_rules! until_required {
    ( $tokens:ident ) => { $tokens.non_exhaustive() };
    ( $tokens:ident [$Token:ident] $( $rest:tt )* ) => { { xor_token!($tokens $Token); $tokens } };
    ( $tokens:ident [$Token:ident?] $( $rest:tt)* ) => { { xor_token!($tokens $Token); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident [$Token:ident*] $( $rest:tt )* ) => { { xor_token!($tokens $Token); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident ($Node:ident $( [] )? ) $( $rest:tt )* ) => { { xor_node!($tokens $Node); $tokens } };
    ( $tokens:ident ($Node:ident?) $( $rest:tt )* ) => { { xor_node!($tokens $Node); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident ($Node:ident[?]) $( $rest:tt )* ) => { { xor_node!($tokens $Node); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident ($Node:ident*) $( $rest:tt )* ) => { { xor_node!($tokens $Node); until_required!( $tokens $( $rest )* ) } };
    ( $tokens:ident ($Node:ident[*]) $( $rest:tt )* ) => { { xor_node!($tokens $Node); until_required!( $tokens $( $rest )* ) } };
}

macro_rules! field_type {
    ( [$Token:ident] ) => { <tokens::$Token as TokenStorage<S>>::Required };
    ( [$Token:ident?] ) => { <tokens::$Token as TokenStorage<S>>::Optional };
    ( [$Token:ident*] ) => { <tokens::$Token as TokenStorage<S>>::Repetition };
    ( ($Node:ident) ) => { $Node<S> };
    ( ($Node:ident[]) ) => { Box<$Node<S>> }; // TODO: just CodeSpan implement for Box<T>
    ( ($Node:ident?) ) => { Option<$Node<S>> }; // TODO: custom type with pos (usize if Style == Full; () otherwise)
    ( ($Node:ident[?]) ) => { Option<Box<$Node<S>>> }; // TODO: re-use new CustomOption<T> replacement
    ( ($Node:ident*) ) => { SmallVec<[$Node<S>; 1]> }; // TODO: custom type with pos (usize if Style == Full; () otherwise)
    ( ($Node:ident[*]) ) => { Vec<$Node<S>> }; // TODO: custom type with pos (usize if Style == Full; () otherwise)
}

/// Pops a concatenation field from the node/token stack.
macro_rules! pop_field {
    ( [$Token:ident] $state:ident ) => {
        tokens::$Token::pop_required($state)
    };
    ( [$Token:ident?] $state:ident ) => {
        tokens::$Token::pop_optional($state)
    };
    ( [$Token:ident*] $state:ident ) => {{
        tokens::$Token::pop_repetition($state)
    }};
    ( ($Node:ident) $state:ident ) => { paste! {
        NodeStack::<S>::pop(&mut $state.nodes.[<$Node:snake>])
    } };
    ( ($Node:ident[]) $state:ident ) => { paste! {
        Box::new(NodeStack::<S>::pop(&mut $state.nodes.[<$Node:snake>]))
    } };
    ( ($Node:ident?) $state:ident ) => { paste! {
        NodeStack::<S>::pop_optional(&mut $state.nodes._optional, &mut $state.nodes.[<$Node:snake>])
    } };
    ( ($Node:ident[?]) $state:ident ) => { paste! {
        NodeStack::<S>::pop_optional(&mut $state.nodes._optional, &mut $state.nodes.[<$Node:snake>]).map(Box::new)
    } };
    ( ($Node:ident*) $state:ident ) => { paste! {
        SmallVec::from_iter(NodeStack::<S>::pop_repetition(&mut $state.nodes._repetition, &mut $state.nodes.[<$Node:snake>]))
    } };
    ( ($Node:ident[*]) $state:ident ) => { paste! {
        Vec::from_iter(NodeStack::<S>::pop_repetition(&mut $state.nodes._repetition, &mut $state.nodes.[<$Node:snake>]))
    } };
}

/// Implements `pop_final_node` for the given concatenation or alternation.
macro_rules! impl_pop_final_node {
    ( $Name:ident ) => {
        paste! {
            fn pop_final_node(nodes: &mut NodeStack<S>) -> Self {
                nodes.[<$Name:snake>].pop().expect("final node should exist")
            }
        }
    };
}

/// Drains nested nodes of a single field into the given [`DroppedNodes`].
macro_rules! drain_field_into_dropped_nodes {
    ( [$Token:ident] $nodes:ident $self:ident $field:ident ) => {};
    ( [$Token:ident?] $nodes:ident $self:ident $field:ident ) => {};
    ( [$Token:ident*] $nodes:ident $self:ident $field:ident ) => {};
    ( ($Node:ident $( [] )? ) $nodes:ident $self:ident $field:ident ) => {
        paste! {
            $self.$field.drain_into_dropped_nodes($nodes);
        }
    };
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

/// At compile time, ensures that the field of a node has no ambiguity caused by a trailing
/// repetition back to the original type.
macro_rules! ensure_no_recursive_node_repetition {
    ( $Name:ident ($Field:ident*) $field:ident ) => {
        ensure_no_recursive_node_repetition_impl!($Name $Field $field)
    };
    ( $Name:ident ($Field:ident[*]) $field:ident ) => {
        ensure_no_recursive_node_repetition_impl!($Name $Field $field)
    };
    ( $Name:ident $Field:tt $field:ident ) => {};
}

/// Pastes the statement only if the field is a node and not a token.
macro_rules! if_node {
    ( ($Node:ident $( $mode:tt )? ) $stmt:tt ) => {
        $stmt
    };
    ( [$Token:ident $( $mode:tt )? ] $stmt:tt ) => {};
}

/// Accesses a field within a [`NodeSet`].
macro_rules! nodes_dot_field {
    ( $nodes:ident ($Field:ident $( $mode:tt )? ) ) => {
        paste! {
            $nodes.[<$Field:snake>]
        }
    };
}

/// Reverses the order of the given list of code blocks.
macro_rules! reverse {
    () => {};
    ( $first:tt $( $rest:tt )* ) => {
        reverse!( $( $rest )* ); $first
    };
}

/// Implements a concatenation node, that supports both optionals and repetitions.
///
/// Fields can be both tokens as well as nodes.
macro_rules! impl_struct_parse {
    ( $Name:ident {
        $( $field:ident: $Field:tt, )*
    } ) => { paste! {
        mod [<$Name:snake>] {
            use enum_map::Enum;

            /// Identifies a single field within a concatenation node.
            #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Enum)]
            pub(crate) enum Field {
                #[default]
                $( [<$field:camel>], )*
            }

            impl Field {
                /// Returns the next field of the concatenation, if one exists.
                pub(crate) fn next(self) -> Option<Self> {
                    let index = self.into_usize();
                    (index < Self::LENGTH - 1).then(|| Self::from_usize(index + 1))
                }
            }
        }

        /// A concatenation node within a grammar.
        pub(crate) struct $Name<S: Style> {
           $( pub(crate) $field: field_type!($Field), )*
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
            /// Expected tokens for a given field, including everything up until and including the next required field.
            const EXPECTED_TOKENS_FROM: EnumMap<[<$Name:snake>]::Field, NestedTokenSet> = EnumMap::from_array({
                let array = PushArray([]);
                repeat_until_empty!(array $( $Field )* ).0
            });

            /// The last required field as well as everything after.
            ///
            /// Used to check for recursion that would lead to ambiguity in the grammar.
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

            /// Moves nodes from `self` into the given [`DroppedNodes`].
            fn drain_into_dropped_nodes(&mut self, nodes: &mut DroppedNodes<S>) {
                $( drain_field_into_dropped_nodes!($Field nodes self $field); )*
            }
        }

        const _: EnumMap<[<$Name:snake>]::Field, NestedTokenSet> = $Name::<Tiny>::EXPECTED_TOKENS_FROM;
        const _: NestedTokenSet = $Name::<Tiny>::EXPECTED_TOKENS;
        const _: () = { $( ensure_no_recursive_node_repetition!($Name $Field $field); )* };

        impl<S: Style> ExpectedTokens for $Name<S> {
            /// Shorthand for the first entry in `EXPECTED_TOKENS_FROM`.
            ///
            /// Implemented in a way that does not introduce cycle compiler errors.
            const EXPECTED_TOKENS: NestedTokenSet = {
                let tokens = NestedTokenSet::new();
                until_required!(tokens $( $Field )* )
            };
        }

        impl<S: Style> ParseImpl<S> for $Name<S> {
            fn parse_iterative(
                state: &mut ParseState<S>,
                expect: Expect,
                field: usize,
                repetition: bool,
            ) -> Result<(), LexerError> {
                if field == [<$Name:snake>]::Field::LENGTH {
                    $( let $field; )*
                    reverse!( $( {
                        $field = pop_field!($Field state)
                    } )* );
                    state.nodes.[<$Name:snake>].push(Self { $( $field, )* });
                    return Ok(());
                }
                if !repetition {
                    state.push_next_field::<Self>(expect, field);
                }
                match [<$Name:snake>]::Field::from_usize(field) { $( [<$Name:snake>]::Field::[<$field:camel>] => {
                    parse_by_mode_iterative!($Field state expect field repetition { expect_field!($Field $Name $field expect) });
                } )* }
                Ok(())
            }

            impl_pop_final_node!($Name);

            fn parse_nested(lexer: &mut CheckedLexer, expect: Expect) -> Result<Self, LexerError> {
                Ok(Self { $( $field: {
                    parse_by_mode!($Field lexer { expect_field!($Field $Name $field expect) })
                }, )* })
            }
        }

        impl<S: Style> Drop for $Name<S> {
            fn drop(&mut self) {
                let mut nodes = DroppedNodes::new();
                self.drain_into_dropped_nodes(&mut nodes);
            }
        }

        impl<S: Style> TryCodeSpan for $Name<S> {
            fn try_code_span(&self) -> Option<Range<usize>> {
                let (first, ..) = ( $( &self.$field, )* );
                let (.., last) = ( $( &self.$field, )* );
                // Some(first.try_code_span()?.start..last.try_code_span()?.end)
                todo!()
            }
        }
    } };
}

/// The type of a node variant.
macro_rules! node_variant_type {
    ( $Node:ident ) => { $Node<S> };
    ( $Node:ident[] ) => { Box<$Node<S>> };
}

/// Wraps a node variant in a box if necessary.
macro_rules! box_variant_if {
    ( $node:tt ) => {
        $node
    };
    ( $node:tt [] ) => {
        Box::new($node)
    };
}

/// Implements an alternation node.
///
/// Variants can be both tokens and nodes.
macro_rules! impl_enum_parse {
    ( $Name:ident {
        $( [$Token:ident], )*
        $( ($Node:ident $( $mode:tt )? ), )*
    } ) => { paste! {
        pub(crate) enum $Name<S: Style> {
            $( $Token(<tokens::$Token as TokenStorage<S>>::Required), )*
            $( $Node(node_variant_type!($Node $( $mode )? )), )*
        }

        impl<S: Style> Clone for $Name<S> {
            fn clone(&self) -> Self {
                match self {
                    $( Self::$Node(node) => Self::$Node(node.clone()), )*
                    $( Self::$Token(token) => Self::$Token(token.clone()), )*
                }
            }
        }

        impl<S: Style> fmt::Debug for $Name<S> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    $( Self::$Node(node) => f.debug_tuple(stringify!($Node)).field(node).finish(), )*
                    $( Self::$Token(_) => write!(f, stringify!($Token)), )*
                }
            }
        }

        impl<S: Style> PartialEq for $Name<S> {
            fn eq(&self, other: &Self) -> bool {
                #[allow(unreachable_patterns)]
                match (self, other) {
                    $( (Self::$Node(node), Self::$Node(other)) => node.eq(other), )*
                    $( (Self::$Token(token), Self::$Token(other)) => token.eq(other), )*
                    _ => false,
                }
            }
        }

        impl<S: Style> Eq for $Name<S> {}

        impl<S: Style> $Name<S> {
            /// The last required field as well as everything after.
            ///
            /// Used to check for recursion that would lead to ambiguity in the grammar.
            const LAST_REQUIRED_AND_NON_EXHAUSTIVE_NODES: NodeSet = NodeSet {
                $( [<$Node:snake>]: true, )*
                ..NodeSet::new()
            };

            /// Moves nodes from `self` into the given [`DroppedNodes`].
            fn drain_into_dropped_nodes(&mut self, nodes: &mut DroppedNodes<S>) {
                match self {
                    $( Self::$Node(node) => node.drain_into_dropped_nodes(nodes), )*
                    _ => {}
                }
            }
        }

        const _: NestedTokenSet = $Name::<Tiny>::EXPECTED_TOKENS;

        impl<S: Style> ExpectedTokens for $Name<S> {
            const EXPECTED_TOKENS: NestedTokenSet = {
                NestedTokenSet::new()
                    $( .xor_without_ambiguity_const(NestedTokenSet::from_kind(TokenKind::$Token)) )*
                    $( .xor_without_ambiguity_const($Node::<Tiny>::EXPECTED_TOKENS) )*
            };
        }

        impl<S: Style> ParseImpl<S> for $Name<S> {
            fn parse_iterative(
                state: &mut ParseState<S>,
                expect: Expect,
                field: usize,
                _repetition: bool,
            ) -> Result<(), LexerError> {
                // token-only alternations never call a build-step, leading to some unreachable code
                #[allow(unreachable_code)]
                if field == 1 {
                    #[allow(unused_variables)]
                    let node = match state.nodes.pop_kind() {
                        $( NodeKind::$Node => Self::$Node(box_variant_if!({ NodeStack::<S>::pop(&mut state.nodes.[<$Node:snake>]) } $( $mode )? )), )*
                        _ => unreachable!("node should match one of the above cases"),
                    };
                    state.nodes.[<$Name:snake>].push(node);
                    return Ok(());
                }

                let found = state.lexer.kind();

                $( if found == TokenKind::$Token {
                    state.nodes.[<$Name:snake>].push(Self::$Token(tokens::$Token::parse_required::<S>(&mut state.lexer, expect)?));
                    return Ok(());
                } )*

                state.push_build_enum::<Self>(expect);

                $( if $Node::<S>::EXPECTED_TOKENS.tokens.contains(found) {
                    state.nodes.push_kind(NodeKind::$Node);
                    state.push_parser::<$Node<S>>(expect);
                    return Ok(());
                } )*

                unreachable!("token should match one of the above cases");
            }

            impl_pop_final_node!($Name);

            fn parse_nested(lexer: &mut CheckedLexer, expect: Expect) -> Result<Self, LexerError> {
                let found = lexer.kind();

                $( if found == TokenKind::$Token {
                    return Ok(Self::$Token(tokens::$Token::parse_required::<S>(lexer, expect)?));
                } )*

                $( if $Node::<S>::EXPECTED_TOKENS.tokens.contains(found) {
                    return Ok(Self::$Node(box_variant_if!({$Node::<S>::parse_nested(lexer, expect)?} $( $mode )? )));
                } )*

                unreachable!("token should match one of the above cases");
            }
        }

        impl<S: Style> TryCodeSpan for $Name<S> {
            fn try_code_span(&self) -> Option<Range<usize>> {
                match self {
                    $( Self::$Node(node) => node.try_code_span(), )*
                    $( Self::$Token(token) => token.try_code_span(), )*
                }
            }
        }
    } };
}

/// Implements a full grammar made up of concatenation and alternation nodes.
macro_rules! impl_node_parse {
    ( $( $kind:ident $Name:ident $content:tt )* ) => { paste! {
        /// The various kinds of nodes.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        enum NodeKind {
            $( $Name, )*
        }

        /// A stack of nodes used by the parser.
        ///
        /// Storage is optimized to be very compact, but care has to be taken, that matching
        /// functions are called in the right order.
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub(crate) struct NodeStack<S: Style> {
            $( [<$Name:snake>]: Vec<$Name<S>>, )*
            _kinds: NodeKinds,
            _optional: BitVec,
            _repetition: Repetition,
        }

        impl<S: Style> NodeStack<S> {
            /// Creates a new empty stack.
            pub(crate) fn new() -> Self {
                Self {
                    $( [<$Name:snake>]: Vec::new(), )*
                    _kinds: NodeKinds::new(),
                    _optional: BitVec::new(),
                    _repetition: Repetition::new(),
                }
            }

            /// Consumes `self` and returns if all fields are empty, which should always be the case
            /// at the end of parsing.
            pub(crate) fn finish(self) -> bool {
                self._optional.is_empty()
                    && self._repetition.is_empty()
                    && $( self.[<$Name:snake>].is_empty() )&&*
            }
        }

        /// A set of node kinds, meant to be used in `const` contexts.
        #[derive(Clone, Copy, Debug)]
        struct NodeSet {
            $( [<$Name:snake>]: bool, )*
        }

        impl NodeSet {
            /// Constructs an empty set.
            const fn new() -> Self {
                Self {
                    $( [<$Name:snake>]: false, )*
                }
            }

            /// Whether the set is empty.
            const fn is_empty(self) -> bool {
                true $( && !self.[<$Name:snake>] )*
            }

            /// Checks for recursion within [`LAST_REQUIRED_AND_NON_EXHAUSTIVE_NODES`].
            ///
            /// - `self` should contain the initial field that is being checked
            /// - `banned_node` should be the node that the field resides in, since a recursion
            ///   back to this type is not allowed
            /// - `checked_nodes` should be empty and is only used for recursion to remember which
            ///   nodes were already checked
            const fn any_recursive_node(self, banned_node: NodeSet, mut checked_nodes: NodeSet) -> bool {
                if self.contains_any(banned_node) {
                    // a field that recurses back to the original node was found
                    return true;
                }

                // no need to check this field again in the future
                checked_nodes = checked_nodes.add(self);

                let mut recursive_nodes = Self::new();

                $( if self.[<$Name:snake>] {
                    recursive_nodes = recursive_nodes.add($Name::<Tiny>::LAST_REQUIRED_AND_NON_EXHAUSTIVE_NODES);
                } )*

                // ignore any of the already checked node kinds
                recursive_nodes = recursive_nodes.remove(checked_nodes);

                // if recursive nodes is empty, no recursion was found; otherwise, recurse
                !recursive_nodes.is_empty() && recursive_nodes.any_recursive_node(banned_node, checked_nodes)
            }

            /// Merges a set with another one.
            const fn add(self, nodes: NodeSet) -> Self {
                Self {
                    $( [<$Name:snake>]: self.[<$Name:snake>] || nodes.[<$Name:snake>], )*
                }
            }

            /// Removes a set of nodes from this one.
            const fn remove(self, nodes: NodeSet) -> Self {
                Self {
                    $( [<$Name:snake>]: self.[<$Name:snake>] && !nodes.[<$Name:snake>], )*
                }
            }

            /// Whether the set contains any of the given nodes.
            const fn contains_any(self, nodes: NodeSet) -> bool {
                $( self.[<$Name:snake>] && nodes.[<$Name:snake>] )||*
            }
        }

        /// Contains a [`Vec`] for each type of node; used to avoid recursion on dropping of nodes.
        struct DroppedNodes<S: Style> {
            $( [<$Name:snake>]: Vec<$Name<S>>, )*
        }

        impl<S: Style> DroppedNodes<S> {
            /// Creates a new empty instance, ready to be filled.
            fn new() -> Self {
                Self { $( [<$Name:snake>]: Vec::new(), )* }
            }
        }

        impl<S: Style> Drop for DroppedNodes<S> {
            /// Drops nodes as well as all their nested nodes without recursion.
            ///
            /// Recursion is avoided by flattening the nested nodes.
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

        $( impl_node_parse!(#inner $kind $Name $content); )*
    } };
    ( #inner struct $Name:ident $content:tt ) => { impl_struct_parse!($Name $content); };
    ( #inner enum $Name:ident $content:tt ) => { impl_enum_parse!($Name $content); };
}

/// A list of [`NodeKind`]s.
type NodeKinds = SmallVec<[NodeKind; 16]>;
const _: () = assert!(std::mem::size_of::<NodeKinds>() <= 24);

/// A list of repetition-end markers.
type Repetition = SmallVec<[usize; 2]>;

impl<S: Style> Default for NodeStack<S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S: Style> NodeStack<S> {
    /// Only pushes a [`NodeKind`].
    ///
    /// This should be accompanied by a matching call to [`Self::push<T>()`].
    fn push_kind(&mut self, kind: NodeKind) {
        self._kinds.push(kind);
    }

    /// Only pops a [`NodeKind`].
    ///
    /// This should be accompanied by a matching call to [`Self::pop<T>()`].
    fn pop_kind(&mut self) -> NodeKind {
        self._kinds.pop().expect("kinds should not be empty")
    }

    /// Pushes a new node into the given stack.
    ///
    /// This should be accompanied by a matching call to [`Self::push_kind()`].
    fn push<T>(fields: &mut Vec<T>, node: T) {
        fields.push(node);
    }

    /// Pops a node from the given stack.
    ///
    /// This should be accompanied by a matching call to [`Self::pop_kind()`].
    fn pop<T>(fields: &mut Vec<T>) -> T {
        fields.pop().expect("fields should not be empty")
    }

    /// Pushes a new marker for an optional node that exists.
    ///
    /// This should therefore be accompanied by pushing of the actual node and kind.
    fn push_some(&mut self) {
        self._optional.push(true);
    }

    /// Pushes a new marker for an optional node that does not exist.
    ///
    /// No node or kind must be pushed in this case.
    fn push_none(&mut self) {
        self._optional.push(false);
    }

    /// Pops an optional node from the given stack.
    ///
    /// `optional` is passed in manually to avoid multiple mutable borrows to `self`.
    fn pop_optional<T>(optional: &mut BitVec, fields: &mut Vec<T>) -> Option<T> {
        optional
            .pop()
            .expect("optional should not be empty")
            .then(|| Self::pop(fields))
    }

    /// Marks the start of a new repetition of a specific kind of node.
    ///
    /// `repetition` is passed in manually to avoid multiple mutable borrows to `self`.
    fn start_repetition<T>(repetition: &mut Repetition, fields: &[T]) {
        repetition.push(fields.len());
    }

    /// Pops a repetition of a specific kind of node as an [`ExactSizeIterator`].
    ///
    /// `repetition` is passed in manually to avoid multiple mutable borrows to `self`.
    fn pop_repetition<'a, T>(
        repetition: &mut SmallVec<[usize; 2]>,
        fields: &'a mut Vec<T>,
    ) -> impl ExactSizeIterator<Item = T> + 'a {
        let start = repetition.pop().expect("repetitions should not be empty");
        fields.drain(start..)
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

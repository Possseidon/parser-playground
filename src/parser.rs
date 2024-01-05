use std::fmt;

use enum_map::EnumMap;
use paste::paste;
use smallvec::SmallVec;

use crate::{
    lexer::{FatalLexerError, TinyLexer},
    push_array::PushArray,
    token::{self, Style, Tiny, TinyToken, Token, TokenKind, TokenSet},
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

    pub(crate) const fn xor_without_ambiguity(self, other: Self) -> Self {
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
struct Expect {
    tokens: TokenSet,
    or_end_of_input: bool,
}

macro_rules! impl_enum_parse {
    ( $( enum $Name:ident {
        $( Tokens: [ $( $Token:ident, )* ] )?
        $( Nodes: [ $( $Node:ident, )* ] )?
    } )* ) => { $(
        #[derive(Clone, Debug)]
        enum $Name<S: Style> {
            $( $( $Token(Token<token::$Token, S>), )* )?
            $( $( $Node($Node<S>), )* )?
        }

        impl<S: Style> $Name<S> {
            const EXPECTED_TOKENS: NestedTokenSet = {
                NestedTokenSet::new()
                    $( $( .xor_without_ambiguity(NestedTokenSet::from_kind(TokenKind::$Token)) )* )?
                    $( $( .xor_without_ambiguity($Node::<S>::EXPECTED_TOKENS) )* )?
            };
        }

        const _: NestedTokenSet = $Name::<Tiny>::EXPECTED_TOKENS;

        impl $Name<Tiny> {
            fn tiny_parse(code: &str) -> Result<Self, FatalLexerError> {
                let mut lexer = TinyLexer::new(code)?;
                check_expected!(lexer (Expect {
                    tokens: Self::EXPECTED_TOKENS.tokens,
                    or_end_of_input: !Self::EXPECTED_TOKENS.exhaustive,
                }));
                Self::tiny_parse_nested(&mut lexer, Expect {
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
        }

        // impl $Name<Positioned> {
        //     fn positioned_parse(lexer: &mut PositionedLexer, errors: &mut Vec<ParseError>) -> Self {
        //         let found = lexer.peek_expected();

        //         $( $( if found == TokenKind::$Token {
        //             return Self::$Token(positioned_parse_token!($Token lexer));
        //         } )* )?

        //         $( $( if $Node::<Tiny>::EXPECTED_TOKENS.tokens.contains(found) {
        //             return Self::$Node(positioned_parse_node!($Node lexer));
        //         } )* )?

        //         unreachable!("token should match one of the above cases");
        //     }
        // }
    )* };
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
        let $tokens = $tokens.xor_without_ambiguity(NestedTokenSet::from_kind(TokenKind::$Token));
    };
}

macro_rules! node {
    ( $tokens:ident $Node:ident ) => {
        let $tokens = $tokens.xor_without_ambiguity($Node::<Tiny>::EXPECTED_TOKENS);
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
    ( $lexer:ident $expect:tt ) => {
        if let Some(next_token) = $lexer.peek() {
            if !$expect.tokens.contains(next_token) {
                return Err(FatalLexerError);
            }
        } else if !$expect.or_end_of_input {
            return Err(FatalLexerError);
        }
    };
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
        let mut expect = $expect;
        // I'm almost certain potential ambiguities on this runtime xor are already prevented by
        // EXPECTED_TOKENS_FROM, but I'm not 100% sure.
        expect.tokens = expect.tokens.xor_without_ambiguity($matches);
        let mut result = $Vec::new();
        while $lexer.peek_matches($matches) {
            result.push($tiny_parse_token_or_node!($TokenOrNode $lexer expect));
        }
        result
    } };
}

macro_rules! tiny_parse_by_mode {
    ( [$Token:tt] $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_token!($Token $lexer $expect)
    };
    ( ($Node:tt) $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_node!($Node $lexer $expect)
    };
    ( [$Token:tt?] $lexer:ident match $matches:tt $expect:tt ) => {
        if $lexer.peek_matches($matches) { Some(tiny_parse_token!($Token $lexer $expect)) } else { None }
    };
    ( ($Node:tt?) $lexer:ident match $matches:tt $expect:tt ) => {
        if $lexer.peek_matches($matches) { Some(tiny_parse_node!($Node $lexer $expect)) } else { None }
    };
    ( ($Node:tt[?]) $lexer:ident match $matches:tt $expect:tt ) => {
        if $lexer.peek_matches($matches) { Some(Box::new(tiny_parse_node!($Node $lexer $expect))) } else { None }
    };
    ( [$Token:tt*] $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_repetition!(tiny_parse_token SmallVec $Token $lexer $matches $expect)
    };
    ( ($Node:tt*) $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_repetition!(tiny_parse_node SmallVec $Node $lexer $matches $expect)
    };
    ( ($Node:tt[*]) $lexer:ident match $matches:tt $expect:tt ) => {
        tiny_parse_repetition!(tiny_parse_node Vec $Node $lexer $matches $expect)
    };
}

macro_rules! impl_struct_parse {
    ( $( struct $Name:ident {
        $( $field:ident: $Field:tt, )*
    } )* ) => { paste! {
        mod struct_fields {
            use enum_map::Enum;

            $(
                #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Enum)]
                pub(crate) enum $Name {
                    #[default]
                    $( [<$field:camel>], )*
                }

                impl $Name {
                    pub(crate) fn next(self) -> Option<Self> {
                        let index = self.into_usize();
                        (index < Self::LENGTH - 1).then(|| Self::from_usize(index + 1))
                    }
                }
            )*
        }

        $(
            struct $Name<S: Style> {
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

            impl<S: Style> $Name<S> {
                /// Expected tokens for a given field only, even if it is not required.
                const EXPECTED_TOKENS_AT: EnumMap<struct_fields::$Name, TokenSet> = EnumMap::from_array([
                    $( expected_tokens!($Field).tokens, )*
                ]);

                /// Expected tokens for a given field, including everything up until the first required field.
                const EXPECTED_TOKENS_FROM: EnumMap<struct_fields::$Name, NestedTokenSet> = EnumMap::from_array({
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

            const _: EnumMap<struct_fields::$Name, TokenSet> = $Name::<Tiny>::EXPECTED_TOKENS_AT;
            const _: EnumMap<struct_fields::$Name, NestedTokenSet> = $Name::<Tiny>::EXPECTED_TOKENS_FROM;
            const _: NestedTokenSet = $Name::<Tiny>::EXPECTED_TOKENS;

            impl $Name<Tiny> {
                fn tiny_parse(code: &str) -> Result<Self, FatalLexerError> {
                    let mut lexer = TinyLexer::new(code)?;
                    check_expected!(lexer (Expect {
                        tokens: Self::EXPECTED_TOKENS.tokens,
                        or_end_of_input: !Self::EXPECTED_TOKENS.exhaustive,
                    }));
                    Self::tiny_parse_nested(&mut lexer, Expect {
                        tokens: TokenSet::new(),
                        or_end_of_input: true,
                    })
                }

                fn tiny_parse_nested(lexer: &mut TinyLexer, expect: Expect) -> Result<Self, FatalLexerError> {
                    Ok(Self { $( $field: {
                        tiny_parse_by_mode!($Field lexer match {
                            Self::EXPECTED_TOKENS_AT[struct_fields::$Name::[<$field:camel>]]
                        } {
                            if let Some(next_field) = struct_fields::$Name::[<$field:camel>].next() {
                                let next_expected_tokens = Self::EXPECTED_TOKENS_FROM[next_field];
                                if next_expected_tokens.exhaustive {
                                    Expect {
                                        tokens: next_expected_tokens.tokens,
                                        or_end_of_input: false,
                                    }
                                } else {
                                    Expect {
                                        // TODO: Check this at compile time or at least in a test if possible.
                                        tokens: next_expected_tokens.tokens.xor_without_ambiguity(expect.tokens),
                                        or_end_of_input: expect.or_end_of_input,
                                    }
                                }
                            } else {
                                expect
                            }
                        })
                    }, )* })
                }
            }
        )*
    } };
}

impl_enum_parse! {
    enum UnaryOperator {
        Tokens: [
            Not,
            Minus,
        ]
    }

    enum BinaryOperator {
        Tokens: [
            Plus,
            Minus,
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

    enum RootExpression {
        Nodes: [
            Literal,
        ]
    }

    enum Literal {
        Tokens: [
            Integer,
            Float,
            String,
            Char,
        ]
    }
}

impl_struct_parse! {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        SelfRepetition::tiny_parse("++").unwrap();
    }
}

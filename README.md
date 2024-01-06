# parser-playground

Me messing around with a parser written in Rust.

While there is already some parser implementation in my [flux-flow](https://github.com/Possseidon/flux-flow) repo (which I also copied parts from into here, especially the lexer), I just wanted a clean slate. And rejoice! So far, the venture was actually quite successful.

The parser is LL(1), i.e. does not have lookahead, but to make up for it, the grammar has various compile time checks that ensure the grammar does not have any ambiguities and the parser should be both memory efficient and *blazingly fast* (I hope at least, lol)

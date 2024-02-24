pub(crate) mod lexer;
pub(crate) mod parser;
pub(crate) mod push_array;
pub(crate) mod token;

use std::{hint::black_box, time::Instant};

use crate::{
    parser::{Parse, Test},
    token::{Full, Tiny},
};

fn measure<T>(code: &str, f: impl Fn(&str) -> T) -> std::time::Duration {
    let now = Instant::now();
    let mut count = 0;
    while now.elapsed() < std::time::Duration::from_millis(1000) {
        count += 1;
        black_box(f(black_box(code)));
    }
    now.elapsed() / count
}

fn main() {
    const COUNT: usize = 1000000;
    // const COUNT: usize = 2;
    let code = "hello 42 ".to_string()
        + &"1.0 ".repeat(COUNT)
        + "fn,fn,"
        + &"fn ".repeat(COUNT)
        + ",struct,mod,fn mod "
        + &"struct ".repeat(COUNT);

    println!("{} bytes", code.len());

    dbg!(measure(&code, |code| Test::<Tiny>::parse_fast(code).unwrap()));
    dbg!(measure(&code, |code| Test::<Tiny>::parse(code).unwrap()));
    dbg!(measure(&code, |code| Test::<Full>::parse_fast(code).unwrap()));
    dbg!(measure(&code, |code| Test::<Full>::parse(code).unwrap()));

    // println!("{test:#?}");
}

use std::fmt::Write;

use ariadne::{Color, Label, Source};
use parser::{lex, parse_string};
use yansi::Paint;

pub fn main() {
    let src = include_str!("../input/test.sw");
    let tokens = lex(src).unwrap();
    let ast = parse_string(&tokens, src).unwrap();
    dbg!(&ast);
    // println!("{}", ast.0);

    let arena = bumpalo::Bump::new();

    // let mut lctx = HirLower::new(&arena);
}


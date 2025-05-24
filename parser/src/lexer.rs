use std::fmt::Display;

use chumsky::{input::BorrowInput, prelude::*, text::ascii::ident};

use crate::{Span, Spanned};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Keyword {
    Class,
    Type,
    Fn,
    Impl,
    For,

    View,
    As,

    I32,
    I64,
    True,
    False,
    F32,
    F64,
    Char,
    Bool,
    If,
    Match,
    Else,
    Let,
    Some,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Punctuation {
    LeftAngle,
    RightAngle,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    Tick,
    Bar,
    Comma,
    Colon,
    ColonColon,

    Arrow,
    Dot,
    Equal,
    Semicolon,
    Plus,
    Star,

    Question,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LiteralTok<'a> {
    Integer(i64),
    Char(&'a str),
    String(&'a str),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<'a> {
    Keyword(Keyword),
    Identifier(&'a str),
    Punctuation(Punctuation),
    Literal(LiteralTok<'a>),
}

pub fn lexer<'src>()
-> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, chumsky::extra::Err<Rich<'src, char, Span>>>
{
    let kw = ident().map(|ident| match ident {
        "class" => Token::Keyword(Keyword::Class),
        "type" => Token::Keyword(Keyword::Type),
        "impl" => Token::Keyword(Keyword::Impl),
        "for" => Token::Keyword(Keyword::For),
        "fn" => Token::Keyword(Keyword::Fn),

        "i32" => Token::Keyword(Keyword::I32),
        "i64" => Token::Keyword(Keyword::I64),
        "f32" => Token::Keyword(Keyword::F32),
        "f64" => Token::Keyword(Keyword::F64),

        "true" => Token::Keyword(Keyword::True),
        "false" => Token::Keyword(Keyword::False),

        "char" => Token::Keyword(Keyword::Char),
        "bool" => Token::Keyword(Keyword::Bool),

        "if" => Token::Keyword(Keyword::If),
        "match" => Token::Keyword(Keyword::Match),
        "else" => Token::Keyword(Keyword::Else),
        "let" => Token::Keyword(Keyword::Let),
        "view" => Token::Keyword(Keyword::View),
        "as" => Token::Keyword(Keyword::As),

        "some" => Token::Keyword(Keyword::Some),
        _ => Token::Identifier(ident),
    });
    let punc = choice((
        // two-wide
        just("->").map(|_| Punctuation::Arrow),
        just("::").map(|_| Punctuation::ColonColon),
        just('<').map(|_| Punctuation::LeftAngle),
        just('>').map(|_| Punctuation::RightAngle),
        just('(').map(|_| Punctuation::LeftParen),
        just(')').map(|_| Punctuation::RightParen),
        just('{').map(|_| Punctuation::LeftBracket),
        just('}').map(|_| Punctuation::RightBracket),
        just('\'').map(|_| Punctuation::Tick),
        just('|').map(|_| Punctuation::Bar),
        just(':').map(|_| Punctuation::Colon),
        just(',').map(|_| Punctuation::Comma),
        just('.').map(|_| Punctuation::Dot),
        just('=').map(|_| Punctuation::Equal),
        just(';').map(|_| Punctuation::Semicolon),
        just('+').map(|_| Punctuation::Plus),
        just('*').map(|_| Punctuation::Star),
        just('?').map(|_| Punctuation::Question),
    ))
    .map(|p| Token::Punctuation(p));

    let int_literal = text::int::<_, _>(10)
        .from_str()
        .unwrapped()
        .map(|i| Token::Literal(LiteralTok::Integer(i)));

    let string = none_of('"')
        .repeated()
        .to_slice()
        .delimited_by(just('"'), just('"'));

    let char_string = just('c')
        .ignore_then(string)
        .map(|content| Token::Literal(LiteralTok::Char(content)));

    let string = string.map(|content| Token::Literal(LiteralTok::String(content)));

    let token = choice((punc, int_literal, string, char_string, kw));
    let comment = just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .padded();

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(comment.repeated())
        .padded()
        .repeated()
        .collect()
}

pub fn make_input<'src>(
    eoi: SimpleSpan,
    toks: &'src [Spanned<Token<'src>>],
) -> impl BorrowInput<'src, Token = Token<'src>, Span = SimpleSpan> {
    toks.map(eoi, |(t, s)| (t, s))
}

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Keyword(keyword) => write!(f, "{:?}", keyword),
            Token::Identifier(s) => write!(f, "{}", s),
            Token::Punctuation(punctuation) => write!(f, "{:?}", punctuation),
            Token::Literal(literal_tok) => write!(f, "{:?}", literal_tok),
        }
    }
}

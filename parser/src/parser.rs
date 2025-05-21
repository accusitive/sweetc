use chumsky::{input::BorrowInput, pratt::{infix, left}, prelude::*};

use crate::{
    Span, Spanned,
    lexer::{Keyword, Punctuation, Token},
};

macro_rules! parser {
    ($t: ty) => {
        impl Parser<'src, I, $t, extra::Err<Rich<'src, Token<'src>>>> + Clone
    };
}
pub type SpannedIdentifier<'a> = Spanned<&'a str>;

#[derive(Debug, Clone)]
pub struct TranslationUnit<'a> {
    pub items: Vec<Spanned<Item<'a>>>,
}
#[derive(Debug, Clone)]
pub struct StructField<'a> {
    pub name: SpannedIdentifier<'a>,
    pub ty: Spanned<Ty<'a>>,
}
#[derive(Debug, Clone)]
pub enum TypeDefinitionKind<'a> {
    Struct {
        fields: Spanned<Vec<Spanned<StructField<'a>>>>,
    },
}
#[derive(Debug, Clone)]
pub enum Item<'a> {
    Function {
        name: SpannedIdentifier<'a>,
        type_parameters: Spanned<Vec<Spanned<TypeParameter<'a>>>>,
        parameters: Spanned<Vec<Spanned<Parameter<'a>>>>,
        returns: Spanned<Ty<'a>>,
        body: Spanned<Expression<'a>>,
    },
    TypeDefinition {
        name: SpannedIdentifier<'a>,
        type_parameters: Spanned<Vec<Spanned<TypeParameter<'a>>>>,
        body: Spanned<TypeDefinitionKind<'a>>,
    },
}
#[derive(Debug, Clone)]
pub struct Parameter<'a> {
    pub name: SpannedIdentifier<'a>,
    pub ty: Spanned<Ty<'a>>,
}
#[derive(Debug, Clone)]
pub struct TypeParameter<'a> {
    pub name: SpannedIdentifier<'a>, // bounds
}

#[derive(Debug, Clone)]
pub enum Ty<'a> {
    Infer,
    I32,
    I64,
    Fn(Spanned<Vec<Spanned<Self>>>, Box<Spanned<Self>>),
    Name(SpannedIdentifier<'a>),
}
#[derive(Debug, Clone)]
pub enum Expression<'a> {
    Path(SpannedIdentifier<'a>),
    Block(Vec<Spanned<Self>>),
    Let(
        SpannedIdentifier<'a>,
        Option<Spanned<Ty<'a>>>,
        Box<Spanned<Self>>,
    ),
    If {
        condition: Box<Spanned<Self>>,
        then: Box<Spanned<Self>>,
        elze: Box<Spanned<Self>>,
    },
    Add(Box<Spanned<Self>>, Box<Spanned<Self>>),
}
pub fn identifier<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(SpannedIdentifier<'src>) {
    select_ref!( Token::Identifier(x) => x).map_with(|s, e| (*s, e.span()))
}
pub fn ty<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<Ty<'src>>) {
    recursive(|ty| {
        let infer = just(Token::Identifier("_")).map(|_| Ty::Infer);
        let int32 = just(Token::Keyword(Keyword::I32)).map(|_| Ty::I32);
        let int64 = just(Token::Keyword(Keyword::I64)).map(|_| Ty::I64);

        let name = identifier().map(|i| Ty::Name(i));

        let params = ty
            .clone()
            .separated_by(just(Token::Punctuation(Punctuation::Comma)))
            .collect::<Vec<_>>()
            .delimited_by(
                just(Token::Punctuation(Punctuation::LeftParen)),
                just(Token::Punctuation(Punctuation::RightParen)),
            )
            .map_with(|x, e| (x, e.span()));

        let func = just(Token::Keyword(Keyword::Fn))
            .ignore_then(params)
            .then_ignore(just(Token::Punctuation(Punctuation::Arrow)))
            .then(ty)
            .map(|(params, ty)| Ty::Fn(params, Box::new(ty)));

        let k = choice((int32, int64, infer, func, name));

        k.map_with(|t, e| (t, e.span()))
    })
}
pub fn type_parameters<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<Vec<Spanned<TypeParameter<'src>>>>) {
    let parameter = identifier().map_with(|i, e| (TypeParameter { name: i }, e.span()));

    parameter
        .separated_by(just(Token::Punctuation(Punctuation::Comma)))
        .collect::<Vec<_>>()
        .delimited_by(
            just(Token::Punctuation(Punctuation::LeftAngle)),
            just(Token::Punctuation(Punctuation::RightAngle)),
        )
        .or_not()
        .map(|x| x.unwrap_or_default())
        .map_with(|params, e| (params, e.span()))
}
pub fn parameters<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<Vec<Spanned<Parameter<'src>>>>) {
    let parameter = identifier()
        .then_ignore(just(Token::Punctuation(Punctuation::Colon)))
        .then(ty())
        .map_with(|(name, ty), e| (Parameter { name, ty }, e.span()));

    parameter
        .separated_by(just(Token::Punctuation(Punctuation::Comma)))
        .collect::<Vec<_>>()
        .delimited_by(
            just(Token::Punctuation(Punctuation::LeftParen)),
            just(Token::Punctuation(Punctuation::RightParen)),
        )
        .map_with(|params, e| (params, e.span()))
}
pub fn expr<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<Expression<'src>>) {
    recursive(|expr| {
        let x = identifier().map_with(|i, e| (Expression::Path(i), e.span()));
        let annotated_let_expr = just(Token::Keyword(Keyword::Let))
            .ignore_then(identifier())
            .then_ignore(just(Token::Punctuation(Punctuation::Colon)))
            .then(ty())
            .then_ignore(just(Token::Punctuation(Punctuation::Equal)))
            .then(expr.clone())
            .map_with(|((identifier, ty), expr), e| {
                (
                    Expression::Let(identifier, Some(ty), Box::new(expr)),
                    e.span(),
                )
            });
        let let_expr = just(Token::Keyword(Keyword::Let))
            .ignore_then(identifier())
            .then_ignore(just(Token::Punctuation(Punctuation::Equal)))
            .then(expr.clone())
            .map_with(|(identifier, expr), e| {
                (Expression::Let(identifier, None, Box::new(expr)), e.span())
            });

        let if_expr = just(Token::Keyword(Keyword::If))
            .ignore_then(expr.clone())
            .then(expr.clone())
            .then_ignore(just(Token::Keyword(Keyword::Else)))
            .then(expr.clone())
            .map_with(|(((condition), then), elze), e| {
                (
                    Expression::If {
                        condition: Box::new(condition),
                        then: Box::new(then),
                        elze: Box::new(elze),
                    },
                    e.span(),
                )
            });

        let block = expr
            .clone()
            .separated_by(just(Token::Punctuation(Punctuation::Semicolon)))
            .collect()
            .delimited_by(
                just(Token::Punctuation(Punctuation::LeftBracket)),
                just(Token::Punctuation(Punctuation::RightBracket)),
            )
            .map_with(|b, e| (Expression::Block(b), e.span()));

        // let add = expr
        //     .clone()
        //     .then_ignore()
        //     .then(expr)
        //     .map_with();
        let atom = choice((block, annotated_let_expr, let_expr, x, if_expr));

        atom.pratt((
            infix(
                left(1),
                just(Token::Punctuation(Punctuation::Plus)),
                |l, op, r, e| (Expression::Add(Box::new(l), Box::new(r)), e.span())
            ),
        ))
    })
}
pub fn item<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<Item<'src>>) {
    let ty_definition_body_struct = identifier::<I>()
        .then_ignore(just(Token::Punctuation(Punctuation::Colon)))
        .then(ty())
        .map_with(|(identifier, ty), e| {
            (
                StructField {
                    name: identifier,
                    ty: ty,
                },
                e.span(),
            )
        })
        .separated_by(just(Token::Punctuation(Punctuation::Comma)))
        .collect::<Vec<_>>()
        .map_with(|fields, e| (fields, e.span()))
        .delimited_by(
            just(Token::Punctuation(Punctuation::LeftBracket)),
            just(Token::Punctuation(Punctuation::RightBracket)),
        )
        .map_with(|fields, e| (TypeDefinitionKind::Struct { fields: fields }, e.span()));

    let ty_definition_body = ty_definition_body_struct;
    let ty_definition = just(Token::Keyword(Keyword::Type))
        .ignore_then(identifier())
        .then(type_parameters())
        .then(ty_definition_body)
        .map_with(|((name, type_parameters), body), e| {
            (
                Item::TypeDefinition {
                    name,
                    type_parameters,
                    body,
                },
                e.span(),
            )
        });

    let func_def = just(Token::Keyword(Keyword::Fn))
        .ignore_then(identifier())
        .then(type_parameters())
        .then(parameters())
        .then_ignore(just(Token::Punctuation(Punctuation::Arrow)))
        .then(ty())
        .then(expr())
        .map_with(|((((ident, type_parameters), parameters), ty), body), e| {
            (
                Item::Function {
                    name: ident,
                    type_parameters,
                    parameters,
                    returns: ty,
                    body,
                },
                e.span(),
            )
        });
    func_def.or(ty_definition)
}
pub fn parser<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<TranslationUnit<'src>>) {
    item()
        .repeated()
        .collect::<Vec<_>>()
        .map_with(|items, e| (TranslationUnit { items }, e.span()))
}

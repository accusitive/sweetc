use chumsky::{
    input::BorrowInput,
    pratt::{infix, left, postfix},
    prelude::*,
};

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
        type_parameters: Vec<Spanned<TypeParameter<'a>>>,
        parameters: Spanned<Vec<Spanned<Parameter<'a>>>>,
        returns: Spanned<Ty<'a>>,
        body: Spanned<Expression<'a>>,
    },
    TypeDefinition {
        name: SpannedIdentifier<'a>,
        type_parameters: Vec<Spanned<TypeParameter<'a>>>,
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
pub struct Path<'a> {
    pub segments: Vec<Spanned<PathSegment<'a>>>,
}
#[derive(Debug, Clone)]
pub struct PathSegment<'a> {
    pub name: SpannedIdentifier<'a>,
    pub ty_arguments: Vec<Spanned<Ty<'a>>>,
}
#[derive(Debug, Clone)]
pub enum Ty<'a> {
    Infer,
    I32,
    I64,
    Bool,
    Fn(Spanned<Vec<Spanned<Self>>>, Box<Spanned<Self>>),
    Name(Path<'a>),
}
#[derive(Debug, Clone)]

pub enum BinaryOperation {
    Add,
    Multiply,
}
#[derive(Debug, Clone)]
pub enum Expression<'a> {
    Path(Path<'a>),
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
    BinaryOperation(Box<Spanned<Self>>, BinaryOperation, Box<Spanned<Self>>),
    Some(Box<Spanned<Self>>),
    Literal(Literal),
    Closure(
        Spanned<Vec<Spanned<Parameter<'a>>>>,
        Spanned<Ty<'a>>,
        Box<Spanned<Self>>,
    ),
    Call(Box<Spanned<Self>>, Vec<Spanned<Self>>),
    X,
}
#[derive(Debug, Clone)]
pub enum Literal {
    Boolean(BooleanLiteral),
}
#[derive(Debug, Clone)]
pub enum BooleanLiteral {
    True,
    False,
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
        let bool = just(Token::Keyword(Keyword::Bool)).map(|_| Ty::Bool);

        // inline so I dont have to deal with recursion, duplicatedin expr
        let segment = identifier()
            .then(
                ty.clone()
                    .separated_by(just(Token::Punctuation(Punctuation::Comma)))
                    .collect::<Vec<_>>()
                    .delimited_by(
                        just(Token::Punctuation(Punctuation::LeftAngle)),
                        just(Token::Punctuation(Punctuation::RightAngle)),
                    )
                    .or_not()
                    .map(|v| v.unwrap_or_default()),
            )
            .map_with(|(name, ty_arguments), e| (PathSegment { name, ty_arguments }, e.span()));

        let path = segment
            .separated_by(just(Token::Punctuation(Punctuation::ColonColon)))
            .at_least(1)
            .collect::<Vec<_>>()
            .map(|segs| Path { segments: segs });

        let name = path.map(|p| Ty::Name(p));

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
            .then(ty.clone())
            .map(|(params, ty)| Ty::Fn(params, Box::new(ty)));

        let main_ty =
            choice((int32, int64, bool, infer, func, name)).map_with(|t, e| (t, e.span()));

        let k = main_ty;

        k
    })
}
pub fn type_parameters<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Vec<Spanned<TypeParameter<'src>>>) {
    let parameter = identifier().map_with(|i, e| (TypeParameter { name: i }, e.span()));

    parameter
        .separated_by(just(Token::Punctuation(Punctuation::Comma)))
        .collect::<Vec<_>>()
        .delimited_by(
            just(Token::Punctuation(Punctuation::LeftAngle)),
            just(Token::Punctuation(Punctuation::RightAngle)),
        )
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
        let r#true = just(Token::Keyword(Keyword::True)).map_with(|i, e| {
            (
                Expression::Literal(Literal::Boolean(BooleanLiteral::True)),
                e.span(),
            )
        });

        let r#false = just(Token::Keyword(Keyword::False)).map_with(|i, e| {
            (
                Expression::Literal(Literal::Boolean(BooleanLiteral::False)),
                e.span(),
            )
        });

        let literal = r#true.or(r#false);

        // inline so I dont have to deal with recursion, duplicatedin expr
        let segment = identifier()
            .then(
                ty().separated_by(just(Token::Punctuation(Punctuation::Comma)))
                    .collect::<Vec<_>>()
                    .delimited_by(
                        just(Token::Punctuation(Punctuation::LeftAngle)),
                        just(Token::Punctuation(Punctuation::RightAngle)),
                    )
                    .or_not()
                    .map(|v| v.unwrap_or_default()),
            )
            .map_with(|(name, ty_arguments), e| (PathSegment { name, ty_arguments }, e.span()));

        let path = segment
            .separated_by(just(Token::Punctuation(Punctuation::ColonColon)))
            .at_least(1)
            .collect::<Vec<_>>()
            .map(|segs| Path { segments: segs });
        let path = path.map_with(|p, e| (Expression::Path(p), e.span()));

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

        let closure = {
            let closure_parameters = parameters();
            just(Token::Keyword(Keyword::Fn))
                .ignore_then(closure_parameters)
                .then_ignore(just(Token::Punctuation(Punctuation::Arrow)))
                .then(ty())
                .then(expr.clone())
        }
        .map_with(|((params, ty), body), e| {
            (Expression::Closure(params, ty, Box::new(body)), e.span())
        });

        let some = just(Token::Keyword(Keyword::Some))
            .ignore_then(expr.clone())
            .map_with(|expr, e| (Expression::Some(Box::new(expr)), e.span()));

        let atom = choice((
            block,
            annotated_let_expr,
            let_expr,
            path,
            if_expr,
            some,
            literal,
            closure,
        ));
        {
            let addition = infix(
                left(1),
                just(Token::Punctuation(Punctuation::Plus)).ignored(),
                |l, _, r, e| {
                    (
                        Expression::BinaryOperation(Box::new(l), BinaryOperation::Add, Box::new(r)),
                        e.span(),
                    )
                },
            );
            let multiplication = infix(
                left(2),
                just(Token::Punctuation(Punctuation::Star)).ignored(),
                |l, _, r, e| {
                    (
                        Expression::BinaryOperation(
                            Box::new(l),
                            BinaryOperation::Multiply,
                            Box::new(r),
                        ),
                        e.span(),
                    )
                },
            );
            let call = postfix(
                0,
                expr.clone()
                    .separated_by(just(Token::Punctuation(Punctuation::Comma)))
                    .collect::<Vec<_>>()
                    .delimited_by(
                        just(Token::Punctuation(Punctuation::LeftParen)),
                        just(Token::Punctuation(Punctuation::RightParen)),
                    ),
                |target, args, e| (Expression::Call(Box::new(target), args), e.span()),
            );

            atom.pratt((addition, multiplication, call))
        }
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
        .then(type_parameters().or_not().map(|x| x.unwrap_or_default()))
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
        .then(type_parameters().or_not().map(|x| x.unwrap_or_default()))
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

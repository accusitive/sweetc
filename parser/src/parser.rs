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
    pub ty: Spanned<TypeExpression<'a>>,
}
#[derive(Debug, Clone)]
pub struct EnumVariant<'a> {
    pub name: SpannedIdentifier<'a>,
    pub fields: Vec<Spanned<TypeExpression<'a>>>,
}
#[derive(Debug, Clone)]
pub enum TypeDefinitionKind<'a> {
    Struct {
        fields: Spanned<Vec<Spanned<StructField<'a>>>>,
    },
    Enum {
        variants: Vec<Spanned<EnumVariant<'a>>>,
    },
}
#[derive(Debug, Clone)]
pub enum Item<'a> {
    Function {
        name: SpannedIdentifier<'a>,
        type_parameters: Spanned<TypeParameters<'a>>,
        parameters: Spanned<Vec<Spanned<Parameter<'a>>>>,
        returns: Spanned<TypeExpression<'a>>,
        body: Spanned<Expression<'a>>,
    },
    Class {
        name: SpannedIdentifier<'a>,
        type_parameters: Spanned<TypeParameters<'a>>,
        items: Vec<Spanned<Item<'a>>>,
    },
    Impl {
        ty: Spanned<TypeExpression<'a>>,
        ty_params: Spanned<TypeParameters<'a>>,
        items: Vec<Spanned<Item<'a>>>,
    },
    ClassFunction {
        name: SpannedIdentifier<'a>,
        type_parameters: Spanned<TypeParameters<'a>>,
        parameters: Spanned<Vec<Spanned<Parameter<'a>>>>,
        returns: Spanned<TypeExpression<'a>>,
    },
    TypeDefinition {
        name: SpannedIdentifier<'a>,
        type_parameters: Spanned<TypeParameters<'a>>,
        body: Spanned<TypeDefinitionKind<'a>>,
    },
}
#[derive(Debug, Clone)]
pub struct Parameter<'a> {
    pub name: SpannedIdentifier<'a>,
    pub ty: Spanned<TypeExpression<'a>>,
}
#[derive(Debug, Clone)]
pub struct TypeParameter<'a> {
    pub name: SpannedIdentifier<'a>, // bounds
    pub parameters: usize,
}
#[derive(Debug, Clone)]
pub struct Path<'a> {
    pub segments: Vec<Spanned<PathSegment<'a>>>,
}
#[derive(Debug, Clone)]
pub struct PathSegment<'a> {
    pub name: SpannedIdentifier<'a>,
    pub ty_arguments: Vec<Spanned<TypeExpression<'a>>>,
}
#[derive(Debug, Clone)]
pub enum TypeExpression<'a> {
    Infer,
    I32,
    I64,
    Bool,
    Fn(Spanned<Vec<Spanned<Self>>>, Box<Spanned<Self>>),
    Name(Path<'a>),
    Tuple(Spanned<Vec<Spanned<Self>>>),
}
#[derive(Debug, Clone)]

pub enum BinaryOperation {
    Add,
    Multiply,
    Pipe,
}
#[derive(Debug, Clone)]
pub enum Expression<'a> {
    Path(Path<'a>),
    Block(Vec<Spanned<Self>>),
    Let(
        Spanned<Pattern<'a>>,
        Option<Spanned<TypeExpression<'a>>>,
        Box<Spanned<Self>>,
        Option<Box<Spanned<Self>>>,
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
        Spanned<TypeExpression<'a>>,
        Box<Spanned<Self>>,
    ),
    Call(Box<Spanned<Self>>, Vec<Spanned<Self>>),
    Ascripted(Box<Spanned<Self>>, Spanned<TypeExpression<'a>>),
    New(Path<'a>, Vec<Spanned<Self>>),
    Match {
        expr: Box<Spanned<Self>>,
        arms: Vec<Spanned<MatchArm<'a>>>,
    },
    Tuple(Vec<Spanned<Self>>),
    X,
}
#[derive(Debug, Clone)]
pub enum Pattern<'a> {
    Wildcard,
    Path(Path<'a>),
    Tuple(Vec<Spanned<Pattern<'a>>>),
}
#[derive(Debug, Clone)]
pub struct MatchArm<'a> {
    pattern: Spanned<Pattern<'a>>,
    expr: Spanned<Expression<'a>>,
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
#[derive(Debug, Clone)]
pub enum Constraint<'a> {
    Impl(Spanned<TypeExpression<'a>>),
    NotImpl(Spanned<TypeExpression<'a>>),
}
#[derive(Debug, Clone)]
pub struct TypeParameters<'a> {
    parameters: Vec<Spanned<TypeParameter<'a>>>,
    constraints: Vec<Spanned<Constraint<'a>>>,
}
pub fn identifier<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(SpannedIdentifier<'src>) {
    select_ref!( Token::Identifier(x) => x).map_with(|s, e| (*s, e.span()))
}
pub fn ty_expr<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<TypeExpression<'src>>) {
    recursive(|ty| {
        let infer = just(Token::Identifier("_")).map(|_| TypeExpression::Infer);
        let int32 = just(Token::Keyword(Keyword::I32)).map(|_| TypeExpression::I32);
        let int64 = just(Token::Keyword(Keyword::I64)).map(|_| TypeExpression::I64);
        let bool = just(Token::Keyword(Keyword::Bool)).map(|_| TypeExpression::Bool);

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

        let name = path.map(|p| TypeExpression::Name(p));

        let params = ty
            .clone()
            .separated_by(just(Token::Punctuation(Punctuation::Comma)))
            .collect::<Vec<_>>()
            .delimited_by(
                just(Token::Punctuation(Punctuation::LeftParen)),
                just(Token::Punctuation(Punctuation::RightParen)),
            )
            .map_with(|x, e| (x, e.span()));

        let tuple = params.clone().map(|p| TypeExpression::Tuple(p));

        let func = just(Token::Keyword(Keyword::Fn))
            .ignore_then(params)
            .then_ignore(just(Token::Punctuation(Punctuation::Arrow)))
            .then(ty.clone())
            .map(|(params, ty)| TypeExpression::Fn(params, Box::new(ty)));

        let main_ty =
            choice((int32, int64, bool, infer, func, name, tuple)).map_with(|t, e| (t, e.span()));

        let k = main_ty;

        k
    })
}
pub fn type_parameters<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<TypeParameters<'src>>) {
    let higher_kinded_parameter = identifier()
        .then(
            just(Token::Punctuation(Punctuation::Question))
                .ignored()
                .separated_by(just(Token::Punctuation(Punctuation::Comma)))
                .collect::<Vec<_>>()
                .delimited_by(
                    just(Token::Punctuation(Punctuation::LeftAngle)),
                    just(Token::Punctuation(Punctuation::RightAngle)),
                )
                .map(|v| v.len()),
        )
        .map_with(|(i, p), e| {
            (
                TypeParameter {
                    name: i,
                    parameters: p,
                },
                e.span(),
            )
        });
    let simple_parameter = identifier().map_with(|i, e| {
        (
            TypeParameter {
                name: i,
                parameters: 0,
            },
            e.span(),
        )
    });
    let parameter = higher_kinded_parameter.or(simple_parameter);

    let params = parameter
        .separated_by(just(Token::Punctuation(Punctuation::Comma)))
        .collect::<Vec<_>>()
        .delimited_by(
            just(Token::Punctuation(Punctuation::LeftAngle)),
            just(Token::Punctuation(Punctuation::RightAngle)),
        );
    let constraint = just(Token::Punctuation(Punctuation::Bang))
        .or_not()
        .then_ignore(just(Token::Keyword(Keyword::Impl)))
        .then(ty_expr())
        .map_with(|(negate, ty), e| {
            (
                match negate {
                    Some(_) => Constraint::NotImpl(ty),
                    None => Constraint::Impl(ty),
                },
                e.span(),
            )
        });

    let constraints = just(Token::Keyword(Keyword::Where)).ignore_then(
        constraint
            .separated_by(just(Token::Punctuation(Punctuation::Comma)))
            .collect()
            .delimited_by(
                just(Token::Punctuation(Punctuation::LeftParen)),
                just(Token::Punctuation(Punctuation::RightParen)),
            ),
    );
    params
        .then(constraints.or_not().map(|x| x.unwrap_or_default()))
        .map_with(|(params, constraints), e| {
            (
                TypeParameters {
                    parameters: params,
                    constraints: constraints,
                },
                e.span(),
            )
        })
        .or_not()
        .map_with(|_, e| {
            (
                TypeParameters {
                    parameters: vec![],
                    constraints: vec![],
                },
                e.span(),
            )
        })
}
pub fn parameters<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<Vec<Spanned<Parameter<'src>>>>) {
    let parameter = identifier()
        .then_ignore(just(Token::Punctuation(Punctuation::Colon)))
        .then(ty_expr())
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
                ty_expr()
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

        let argument_list = expr
            .clone()
            .separated_by(just(Token::Punctuation(Punctuation::Comma)))
            .collect::<Vec<_>>()
            .delimited_by(
                just(Token::Punctuation(Punctuation::LeftParen)),
                just(Token::Punctuation(Punctuation::RightParen)),
            );

        let new = just(Token::Keyword(Keyword::New))
            .ignore_then(path.clone())
            .then(
                argument_list
                    .clone()
                    .or_not()
                    .map(|x| x.unwrap_or_default()),
            )
            .map_with(|(p, a), e| (Expression::New(p, a), e.span()));

        let path = path.map_with(|p, e| (Expression::Path(p), e.span()));

        // let annotated_let_expr = just(Token::Keyword(Keyword::Let))
        //     .ignore_then(identifier())
        //     .then_ignore(just(Token::Punctuation(Punctuation::Colon)))
        //     .then(ty_expression())
        //     .then_ignore(just(Token::Punctuation(Punctuation::Equal)))
        //     .then(expr.clone())
        //     .map_with(|((identifier, ty), expr), e| {
        //         (
        //             Expression::Let(identifier, Some(ty), Box::new(expr)),
        //             e.span(),
        //         )
        //     });
        let let_expr = just(Token::Keyword(Keyword::Let))
            .ignore_then(pattern())
            .then_ignore(just(Token::Punctuation(Punctuation::Equal)))
            .then(expr.clone())
            .then(expr.clone().or_not())
            .map_with(|((identifier, expr), next), e| {
                (
                    Expression::Let(identifier, None, Box::new(expr), next.map(|v| Box::new(v))),
                    e.span(),
                )
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
                .then(ty_expr())
                .then(expr.clone())
        }
        .map_with(|((params, ty), body), e| {
            (Expression::Closure(params, ty, Box::new(body)), e.span())
        });

        let some = just(Token::Keyword(Keyword::Some))
            .ignore_then(expr.clone())
            .map_with(|expr, e| (Expression::Some(Box::new(expr)), e.span()));
        let paren = expr.clone().delimited_by(
            just(Token::Punctuation(Punctuation::LeftParen)),
            just(Token::Punctuation(Punctuation::RightParen)),
        );
        let match_arm = just(Token::Punctuation(Punctuation::Bar))
            .ignore_then(pattern())
            .then_ignore(just(Token::Punctuation(Punctuation::FatArrow)))
            .then(expr.clone())
            .map_with(|(pattern, expr), e| (MatchArm { pattern, expr }, e.span()));

        let r#match = just(Token::Keyword(Keyword::Match))
            .ignore_then(expr.clone())
            .then(match_arm.repeated().collect::<Vec<_>>().delimited_by(
                just(Token::Punctuation(Punctuation::LeftBracket)),
                just(Token::Punctuation(Punctuation::RightBracket)),
            ))
            .map_with(|(expr, arms), e| {
                (
                    Expression::Match {
                        expr: Box::new(expr),
                        arms,
                    },
                    e.span(),
                )
            });

        let tuple = expr
            .clone()
            .separated_by(just(Token::Punctuation(Punctuation::Comma)))
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(
                just(Token::Punctuation(Punctuation::LeftParen)),
                just(Token::Punctuation(Punctuation::RightParen)),
            )
            .map_with(|exprs, e| (Expression::Tuple(exprs), e.span()));
        let atom = choice((
            tuple, paren, block, let_expr, new, path, if_expr, some, literal, closure, r#match,
        ));
        {
            let pipe = infix(
                left(0),
                just(Token::Punctuation(Punctuation::Pipe)).ignored(),
                |l, _, r, e| {
                    (
                        Expression::BinaryOperation(
                            Box::new(l),
                            BinaryOperation::Pipe,
                            Box::new(r),
                        ),
                        e.span(),
                    )
                },
            );
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

            let call = postfix(1, argument_list, |target, args, e| {
                (Expression::Call(Box::new(target), args), e.span())
            });

            let ascription = postfix(
                5,
                just(Token::Punctuation(Punctuation::Colon)).ignore_then(ty_expr()),
                |target, ty, e| (Expression::Ascripted(Box::new(target), ty), e.span()),
            );

            atom.pratt((addition, multiplication, call, ascription, pipe))
        }
    })
}
pub fn pattern<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<Pattern<'src>>) {
    let wildcard = just(Token::Identifier("_"))
        .ignored()
        .map_with(|_, e| (Pattern::Wildcard, e.span()));

    let segment = identifier()
        .then(
            ty_expr()
                .clone()
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

    let path = path.map_with(|p, e| (Pattern::Path(p), e.span()));

    let base = choice((wildcard, path));

    recursive(|pattern| {
        let tuple = pattern
            .separated_by(just(Token::Punctuation(Punctuation::Comma)))
            .allow_trailing()
            .collect()
            .delimited_by(
                just(Token::Punctuation(Punctuation::LeftParen)),
                just(Token::Punctuation(Punctuation::RightParen)),
            )
            .map_with(|p, e| (Pattern::Tuple(p), e.span()));

        tuple.or(base)
    })
}
pub fn item<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<Item<'src>>) {
    let enum_variant = identifier()
        .then(
            ty_expr()
                .separated_by(just(Token::Punctuation(Punctuation::Comma)))
                .collect::<Vec<_>>()
                .delimited_by(
                    just(Token::Punctuation(Punctuation::LeftParen)),
                    just(Token::Punctuation(Punctuation::RightParen)),
                )
                .or_not()
                .map(|x| x.unwrap_or_default()),
        )
        .map_with(|(name, fields), e| (EnumVariant { name, fields }, e.span()));
    let ty_definition_body_enum = enum_variant
        .separated_by(just(Token::Punctuation(Punctuation::Bar)))
        .allow_trailing()
        .allow_leading()
        .collect::<Vec<_>>()
        .delimited_by(
            just(Token::Punctuation(Punctuation::LeftBracket)),
            just(Token::Punctuation(Punctuation::RightBracket)),
        )
        .map_with(|variants, e| (TypeDefinitionKind::Enum { variants }, e.span()));

    let ty_definition_body_struct = identifier()
        .then_ignore(just(Token::Punctuation(Punctuation::Colon)))
        .then(ty_expr())
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
        .allow_trailing()
        .collect::<Vec<_>>()
        .map_with(|fields, e| (fields, e.span()))
        .delimited_by(
            just(Token::Punctuation(Punctuation::LeftBracket)),
            just(Token::Punctuation(Punctuation::RightBracket)),
        )
        .map_with(|fields, e| (TypeDefinitionKind::Struct { fields: fields }, e.span()));

    let ty_definition_body = ty_definition_body_enum.or(ty_definition_body_struct);
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
        .then_ignore(just(Token::Punctuation(Punctuation::Colon)))
        .then(parameters())
        .then_ignore(just(Token::Punctuation(Punctuation::Arrow)))
        .then(ty_expr())
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

    let class_fn = just(Token::Keyword(Keyword::Fn))
        .ignore_then(identifier())
        .then(type_parameters())
        .then_ignore(just(Token::Punctuation(Punctuation::Colon)))
        .then(parameters())
        .then_ignore(just(Token::Punctuation(Punctuation::Arrow)))
        .then(ty_expr())
        .map_with(|(((ident, type_parameters), parameters), ty), e| {
            (
                Item::ClassFunction {
                    name: ident,
                    type_parameters,
                    parameters,
                    returns: ty,
                },
                e.span(),
            )
        });
    let class_fns = class_fn.repeated().collect::<Vec<_>>();

    let class_def = just(Token::Keyword(Keyword::Class))
        .ignore_then(identifier())
        .then(type_parameters())
        .then(class_fns.delimited_by(
            just(Token::Punctuation(Punctuation::LeftBracket)),
            just(Token::Punctuation(Punctuation::RightBracket)),
        ))
        .map_with(|((name, type_parameters), items), e| {
            (
                Item::Class {
                    name,
                    type_parameters,
                    items,
                },
                e.span(),
            )
        });
    let impl_body = func_def.clone().repeated().collect::<Vec<_>>();

    let r#impl = just(Token::Keyword(Keyword::Impl))
        .ignore_then(type_parameters())
        .then(ty_expr())
        .then(impl_body.delimited_by(
            just(Token::Punctuation(Punctuation::LeftBracket)),
            just(Token::Punctuation(Punctuation::RightBracket)),
        ))
        .map_with(|((ty_params, ty), items), e| {
            (
                Item::Impl {
                    ty,
                    ty_params,
                    items,
                },
                e.span(),
            )
        });

    choice((func_def, ty_definition, class_def, r#impl))
}
pub fn parser<'src, I: BorrowInput<'src, Token = Token<'src>, Span = Span>>()
-> parser!(Spanned<TranslationUnit<'src>>) {
    item()
        .repeated()
        .collect::<Vec<_>>()
        .map_with(|items, e| (TranslationUnit { items }, e.span()))
}

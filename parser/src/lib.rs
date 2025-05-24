#![feature(iter_intersperse)]
use std::{
    fmt::{Display, Write, write},
    ops::Deref,
};

use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::prelude::*;

use lexer::Token;
use parser::{
    BinaryOperation, Expression, Item, Parameter, Path, PathSegment, TranslationUnit, TyExpression,
    TypeDefinitionKind, TypeParameter,
};

pub type Span = SimpleSpan;
pub type Spanned<T> = (T, Span);

pub mod lexer;
pub mod parser;

pub fn lex<'src>(src: &'src str) -> Option<Vec<Spanned<Token<'src>>>> {
    let (tokens, errs) = lexer::lexer().parse(src).into_output_errors();
    if let Some(toks) = tokens {
        return Some(toks);
    }

    errs.into_iter().for_each(|e| {
        Report::build(ReportKind::Error, ((), e.span().into_range()))
            .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
            .with_message(e.to_string())
            .with_label(
                Label::new(((), e.span().into_range()))
                    .with_message(e.reason().to_string())
                    .with_color(Color::Red),
            )
            .finish()
            .print(Source::from(&src))
            .unwrap()
    });
    None
}
pub fn parse_string<'src>(
    tokens: &'src [Spanned<Token<'src>>],
    src: &'src str,
) -> Option<Spanned<TranslationUnit<'src>>> {
    let input = lexer::make_input(SimpleSpan::new((), 0..src.len()), tokens);
    let (ast, errs) = crate::parser::parser().parse(input).into_output_errors();
    if let Some(ast) = ast {
        return Some(ast);
    }

    errs.into_iter().for_each(|e| {
        Report::build(ReportKind::Error, ((), e.span().into_range()))
            .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
            .with_message("Error while parsing")
            .with_label(
                Label::new(((), e.span().into_range()))
                    .with_message(e.reason())
                    .with_color(Color::Red),
            )
            .finish()
            .print(Source::from(&src))
            .unwrap()
    });

    None
}

// impl<'a> Display for TranslationUnit<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         for item in &self.items {
//             writeln!(f, "{}", item.0)?;
//         }
//         Ok(())
//     }
// }

// impl<'a> Display for Item<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             Item::Function {
//                 name,
//                 type_parameters,
//                 parameters,
//                 returns,
//                 body,
//             } => {
//                 write!(f, "fn {}", name.0)?;
//                 if type_parameters.len() > 0 {
//                     write!(f, "<")?;
//                     for tp in type_parameters {
//                         write!(f, "{}, ", tp.0.name.0)?;
//                     }
//                     write!(f, ">")?;
//                 }

//                 write!(f, "(")?;
//                 for param in &parameters.0 {
//                     write!(f, "{}, ", param.0)?;
//                 }
//                 write!(f, ")")?;
//                 write!(f, " -> {}", returns.0)?;
//                 write!(f, "\n{}", body.0)?;
//             }
//             Item::TypeDefinition {
//                 name,
//                 type_parameters,
//                 body,
//             } => {
//                 write!(f, "type {}", name.0)?;
//                 if type_parameters.len() > 0 {
//                     write!(f, "<")?;
//                     for tp in type_parameters {
//                         write!(f, "{}, ", tp.0.name.0)?;
//                     }
//                     write!(f, ">")?;
//                 }
//                 write!(f, "{}", body.0)?;
//             }
//         }
//         Ok(())
//     }
// }

// impl<'a> Display for Parameter<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{}: {}", self.name.0, self.ty.0)
//     }
// }
// impl<'a> Display for Ty<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             Ty::I32 => {
//                 write!(f, "i32")?;
//             }
//             Ty::I64 => {
//                 write!(f, "i64")?;
//             }
//             Ty::Fn(params, returns) => {
//                 write!(f, "fn")?;
//                 write!(f, "(")?;
//                 for param in &params.0 {
//                     write!(f, "{}, ", param.0)?;
//                 }
//                 write!(f, ")")?;
//                 write!(f, " -> ")?;
//                 write!(f, " {}", returns.0)?;
//             }
//             Ty::Infer => {
//                 write!(f, "_")?;
//             }
//             Ty::Name(n) => {
//                 write!(f, "{}", n)?;
//             }
//             // Ty::Apply(base, params) => {
//             //     write!(f, "{}", base.deref().0)?;
//             //     write!(f, "<")?;
//             //     for param in params {
//             //         write!(f, "{}, ", param.0)?;
//             //     }
//             //     write!(f, ">")?;
//             // }
//             Ty::Bool => {
//                 write!(f, "bool")?;
//             }
//         }
//         return Ok(());
//     }
// }
// impl<'a> Display for TypeParameter<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{}", self.name.0)
//     }
// }
// impl<'a> Display for Expression<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         let mut s = String::new();

//         match self {
//             Expression::Path(i) => {
//                 s.write_str(i.0)?;
//             }
//             Expression::Block(items) => {
//                 write!(s, "{{")?;
//                 for (item, _) in items {
//                     write!(s, "\n{}", item)?;
//                 }
//                 write!(s, "$$NL$$}}")?;
//             }
//             Expression::Let(binding, Some(ty), expr) => {
//                 write!(s, "let {}: {} = {}", binding.0, ty.0, expr.deref().0)?;
//             }
//             Expression::Let(binding, None, expr) => {
//                 write!(s, "let {} = {}", binding.0, expr.deref().0)?;
//             }
//             Expression::If {
//                 condition,
//                 then,
//                 elze,
//             } => {
//                 write!(s, "if {} ", condition.deref().0)?;
//                 write!(s, "{}\n", then.deref().0)?;
//                 write!(s, "else {}", elze.deref().0)?;
//             }
//             Expression::BinaryOperation(l, op, r) => {
//                 write!(s, "{} {} {}", l.deref().0, op, r.deref().0)?;
//             }
//             Expression::Some(inner) => {
//                 write!(f, "some {}", inner.deref().0)?;
//             }
//             Expression::Literal(literal) => match literal {
//                 parser::Literal::Boolean(boolean_literal) => match boolean_literal {
//                     parser::BooleanLiteral::True => {
//                         write!(f, "true")?;
//                     }
//                     parser::BooleanLiteral::False => {
//                         write!(f, "false")?;
//                     }
//                 },
//             },
//             Expression::Closure(params, returns, body) => {
//                 write!(f, "fn")?;
//                 write!(f, "(")?;
//                 for param in &params.0 {
//                     write!(f, "{}, ", param.0)?;
//                 }
//                 write!(f, ")")?;
//                 write!(f, " -> ")?;
//                 write!(f, " {}", returns.0)?;
//             }
//             Expression::Call(target, items) => {
//                 write!(f, "{}", target.deref().0)?;
//                 write!(f, "(")?;
//                 for item in items {
//                     write!(f, "{}, ", item.0)?;
//                 }
//                 write!(f, ")")?;
//             }
//             Expression::X => todo!(),
//         }
//         f.write_str(
//             &s.lines()
//                 .intersperse("\n    ")
//                 .collect::<String>()
//                 .replace("$$NL$$", "\n"),
//         )?;
//         Ok(())
//     }
// }

// impl<'a> Display for TypeDefinitionKind<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             TypeDefinitionKind::Struct { fields } => {
//                 write!(f, "{{\n")?;
//                 for field in &fields.0 {
//                     write!(f, "    {}: {},\n", field.0.name.0, field.0.ty.0)?;
//                 }
//                 write!(f, "}}")?;
//             }
//         }
//         Ok(())
//     }
// }

// impl<'a> Display for BinaryOperation {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             BinaryOperation::Add => write!(f, "+"),
//             BinaryOperation::Multiply => write!(f, "*"),
//         }
//     }
// }
// impl<'a> Display for Path<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         for segment in &self.segments {
//             write!(f, "{}", segment.0)?;
//         }
//         Ok(())
//     }
// }
// impl<'a> Display for PathSegment<'a> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{}", self.name.0)?;
//         write!(f, "<")?;
//         for param in &self.ty_arguments {
//             write!(f, "{}, ", param.0)?;
//         }
//         write!(f, ">")?;
//         Ok(())
//     }
// }

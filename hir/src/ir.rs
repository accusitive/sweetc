use std::{collections::HashMap, fmt::Display};

use crate::ast;
use crate::{DefId, HirId};
use parser::Spanned;
use parser::{Span, parser::SpannedIdentifier};

pub type Subs = HashMap<usize, TyKind>;
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TyKind {
    I32,
    I64,
    Bool,

    // Internal type for inference
    Unspecified(usize),
    // Reference to a definition, ie: Type Parameter, Struct, Enum, type Alias
    Local(DefId),
    // Base<A,R,G,S>
    Apply(Box<Ty>, Vec<Ty>),

    Function(Vec<Ty>, Box<Ty>),
}
#[derive(Debug)]
pub struct FunctionDefinition<'src> {
    pub name: SpannedIdentifier<'src>,
    pub type_parameters: Vec<Spanned<ast::TypeParameter<'src>>>,
    pub parameters: Vec<DefId>,
    pub body: HirId,
    pub ty: Ty,
}
#[derive(Debug)]
pub struct StructDefinition<'src> {
    pub name: SpannedIdentifier<'src>,
    pub fields: Vec<StructField<'src>>,
}
#[derive(Debug)]
pub struct StructField<'src> {
    pub ident: SpannedIdentifier<'src>,
    pub ty: Ty,
    pub span: Span,
}
#[derive(Debug)]
pub struct Parameter {
    pub def_id: DefId,
    pub ty: Ty,
    pub span: Span,
}
#[derive(Debug)]
pub struct Expression<'hir> {
    pub id: HirId,
    pub kind: ExprKind<'hir>,
    pub span: Span,
}
#[derive(Debug)]
pub enum ExprKind<'hir> {
    Block(&'hir [&'hir Expression<'hir>]),
    Let(&'hir Expression<'hir>),
    If(
        &'hir Expression<'hir>,
        &'hir Expression<'hir>,
        &'hir Expression<'hir>,
    ),
    BinaryOperation(
        &'hir Expression<'hir>,
        ast::BinaryOperation,
        &'hir Expression<'hir>,
    ),
    Local(Vec<Ty>, DefId),
    Some(&'hir Expression<'hir>),
    Literal(ast::Literal),
    Closure(TyKind, &'hir Expression<'hir>),
    Call(&'hir Expression<'hir>, &'hir [&'hir Expression<'hir>]),
    Z
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}
impl Display for TyKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyKind::I32 => write!(f, "i32"),
            TyKind::I64 => write!(f, "i64"),
            TyKind::Unspecified(num) => write!(f, "_{num}"),
            TyKind::Local(def_id) => write!(f, "_local{}", def_id.0),
            TyKind::Apply(ty, items) => {
                write!(f, "{}", ty)?;
                write!(f, "<")?;
                for (item, i) in items.iter().zip(0..) {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, ">")
            }
            TyKind::Bool => write!(f, "bool"),
            TyKind::Function(items, ty) => {
                write!(f, "fn")?;
                write!(f, "(")?;
                for (item, i) in items.iter().zip(0..) {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")?;

                write!(f, " -> {}", ty)
            }
        }
    }
}

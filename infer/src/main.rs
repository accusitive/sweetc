use std::{collections::HashMap, fmt::Display};

use lang::{Expression, Inference};
mod lang;
fn main() {
    // let add_two_numbers = Ty::Fn {
    //     param: Box::new(Ty::Constructor("i32", Kind::Star)),
    //     returns: Box::new(Ty::Fn {
    //         param: Box::new(Ty::Constructor("i32", Kind::Star)),
    //         returns: Box::new(Ty::Constructor("i32", Kind::Star)),
    //     }),
    // };
    // println!("{}", add_two_numbers);
    // let some_fn = Ty::Fn {
    //     param: Box::new(Ty::TypeVariable('T')),
    //     returns: Box::new(Ty::App {
    //         constructor: Box::new(Ty::Constructor(
    //             "Option",
    //             Kind::Pointer(Box::new(Kind::Star)),
    //         )),
    //         argument: Box::new(Ty::TypeVariable('T')),
    //     }),
    // };
    // println!("{}", some_fn);

    // let sub = unify(
    //     &Ty::TypeVariable('T'),
    //     &Ty::Constructor("i32", Kind::Star),
    //     Substitutions::new(),
    // )
    // .unwrap();

    // dbg!(&sub);

    // println!("{}", apply(&some_fn, &sub))

    // let x_42 = Expression {
    //     kind: lang::ExprKind::Literal(42),
    // };
    // let x_100 = Expression {
    //     kind: lang::ExprKind::Literal(100),
    // };
    // let sum0 = Expression {
    //     kind: lang::ExprKind::BinOp(Box::new(x_42), lang::Operator::Add, Box::new(x_100)),
    // };

    // let x_420 = Expression {
    //     kind: lang::ExprKind::Literal(42),
    // };
    // let x_1000 = Expression {
    //     kind: lang::ExprKind::Literal(100),
    // };
    // let sum1 = Expression {
    //     kind: lang::ExprKind::BinOp(Box::new(x_420), lang::Operator::Add, Box::new(x_1000)),
    // };

    // let product = Expression {
    //     kind: lang::ExprKind::BinOp(Box::new(sum0), lang::Operator::Multiply, Box::new(sum1)),
    // };

    // let f = Expression{
    //     kind: lang::ExprKind::Closure(Ty::Constructor("i64", Kind::Star), Box::new(product))
    // };

    let param = Expression {
        kind: lang::ExprKind::Identifier("param"),
    };
    let x_42 = Expression {
        kind: lang::ExprKind::Literal(42),
    };

    let sum = Expression {
        kind: lang::ExprKind::BinOp(Box::new(param), lang::Operator::Add, Box::new(x_42)),
    };

    // let some = Expression {
    //     kind: lang::ExprKind::Some(Box::new(param)),
    // };

    let mut type_environment = HashMap::new();
    type_environment.insert("param", Ty::ConcreteTy(ConcreteTy::I64));

    let mut env = Inference {
        type_var_counter: 100,
        constraints: vec![],
        substitutions: HashMap::new(),
        type_environment,
    };
    let typed = env.create_typed_expression_tree(&sum).unwrap();

    dbg!(&typed);
    env.create_substitutions();
    env.update_type_environment();

    let z = env.resolved(&typed);
    dbg!(&z);
    println!("{}", z.ty);
}
type Substitutions = HashMap<usize, Ty>;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ConcreteTy {
    Integer,
    I32,
    I64,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Ty {
    TypeVariable(usize),
    Fn {
        param: Box<Ty>,
        returns: Box<Ty>,
    },
    ConcreteTy(ConcreteTy),
    Constructor(&'static str, Kind),

    /// A type application like Option<a> or Result<a b>
    App {
        constructor: Box<Ty>,
        argument: Box<Ty>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Kind {
    Star,
    Pointer(Box<Self>),
}

// fn occurs_check(var: &Ty, other: &Ty, sub: &HashMap<char, Ty>) -> bool {
//     match other {
//         Ty::TypeVariable(v) => {
//             if let Some(t) = sub.get(v) {
//                 occurs_check(var, t, sub)
//             } else {
//                 var == other
//             }
//         }
//         Ty::Fn { param, returns } => {
//             occurs_check(var, param, sub) || occurs_check(var, returns, sub)
//         }
//         Ty::App {
//             constructor,
//             argument,
//         } => occurs_check(var, constructor, sub) || occurs_check(var, argument, sub),
//         _ => var == other,
//     }
// }

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::TypeVariable(c) => write!(f, "'{}", c),
            Ty::Fn { param, returns } => write!(f, "(fn({}) -> {})", param, returns),
            Ty::Constructor(name, kind) => write!(f, "{}[{}]", name, kind),
            Ty::App {
                constructor,
                argument,
            } => write!(f, "{}<{}>", constructor, argument),
            Ty::ConcreteTy(concrete_ty) => match concrete_ty {
                ConcreteTy::Integer => write!(f, "int"),
                ConcreteTy::I32 => write!(f, "i32"),
                ConcreteTy::I64 => write!(f, "i64"),
            },
        }
    }
}

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Star => write!(f, "*"),
            Kind::Pointer(kind) => write!(f, "*->{}", kind),
        }
    }
}

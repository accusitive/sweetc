use std::collections::HashMap;

use crate::{ConcreteTy, Kind, Substitutions, Ty};

#[derive(Debug)]
pub struct Expression {
    pub(crate) kind: ExprKind<Box<Self>>,
}
#[derive(Debug, Clone)]
pub enum Constraint {
    Equal(Ty),
}
#[derive(Debug, Clone)]
pub struct TypedExpression {
    pub kind: ExprKind<Box<TypedExpression>>,
    pub ty: Ty,
}
#[derive(Debug, Clone)]
pub enum ExprKind<E> {
    BinOp(E, Operator, E),
    Literal(i64),
    Closure(Ty, E),
    Identifier(&'static str),

    Some(E),
}
#[derive(Debug, Clone)]
pub enum Operator {
    Add,
    Subtract,
    Multiply,
    Divide,
}

pub struct Inference {
    pub type_var_counter: usize,
    pub constraints: Vec<(Ty, Ty)>,
    pub substitutions: Substitutions,
    pub type_environment: HashMap<&'static str, Ty>,
}

impl Inference {
    fn next_type_var(&mut self) -> usize {
        let next = self.type_var_counter;
        self.type_var_counter += 1;

        next
    }
    pub fn create_typed_expression_tree<'a>(
        &mut self,
        e: &Expression,
    ) -> Result<TypedExpression, &'a str> {
        match &e.kind {
            ExprKind::BinOp(lhs, operator, rhs) => {
                let tv = self.next_type_var();

                let tlhs = self.create_typed_expression_tree(&*lhs)?;
                let trhs = self.create_typed_expression_tree(&*rhs)?;

                self.constraints.push((tlhs.ty.clone(), trhs.ty.clone()));
                self.constraints
                    .push((Ty::TypeVariable(tv), tlhs.ty.clone()));
                self.constraints
                    .push((Ty::TypeVariable(tv), trhs.ty.clone()));

                Ok(TypedExpression {
                    kind: ExprKind::BinOp(Box::new(tlhs), operator.clone(), Box::new(trhs)),
                    ty: Ty::TypeVariable(tv),
                })
            }
            ExprKind::Closure(param, body) => {
                let tv = self.next_type_var();
                let body = self.create_typed_expression_tree(&*body)?;

                self.constraints
                    .push((Ty::TypeVariable(tv), body.ty.clone()));

                Ok(TypedExpression {
                    kind: ExprKind::Closure(param.clone(), Box::new(body)),
                    ty: Ty::Fn {
                        param: Box::new(param.clone()),
                        returns: Box::new(Ty::TypeVariable(tv)),
                    },
                })
            }
            ExprKind::Literal(int) => Ok(TypedExpression {
                kind: ExprKind::Literal(*int),
                ty: Ty::ConcreteTy(crate::ConcreteTy::Integer)
            }),
            ExprKind::Identifier(i) => {
                let ty = self
                    .type_environment
                    .get(i)
                    .clone()
                    .expect(&format!("failed to find type {} in env", i));

                Ok(TypedExpression {
                    kind: ExprKind::Identifier(i),
                    ty: ty.clone(),
                })
            }
            ExprKind::Some(e) => {
                let t = self.create_typed_expression_tree(&*e)?;
                let tt = t.ty.clone();
                Ok(TypedExpression {
                    kind: ExprKind::Some(Box::new(t)),
                    ty: Ty::App {
                        constructor: Box::new(Ty::Constructor(
                            "Option",
                            Kind::Pointer(Box::new(Kind::Star)),
                        )),
                        argument: Box::new(tt),
                    },
                })
            }
        }
    }
    pub fn create_substitutions(&mut self) {
        let mut sub = std::mem::take(&mut self.substitutions);

        for (lhs, rhs) in &self.constraints {
            sub = unify(lhs, rhs, sub).unwrap();
        }
        self.substitutions = sub;
    }
    pub fn update_type_environment(&mut self) {
        for (k, v) in self.type_environment.iter_mut() {
            *v = apply(v, &self.substitutions);
        }
    }
    pub fn resolved(&mut self, expr: &TypedExpression) -> TypedExpression {
        match &expr.kind {
            ExprKind::BinOp(lhs, operator, rhs) => TypedExpression {
                kind: ExprKind::BinOp(
                    Box::new(self.resolved(&*lhs)),
                    operator.clone(),
                    Box::new(self.resolved(&*rhs)),
                ),
                ty: apply(&expr.ty, &self.substitutions),
            },
            ExprKind::Closure(param, body) => TypedExpression {
                kind: ExprKind::Closure(param.clone(), Box::new(self.resolved(&*body))),
                ty: apply(&expr.ty, &self.substitutions),
            },
            ExprKind::Literal(_) => expr.clone(),
            ExprKind::Identifier(i) => {
                let t = &self.type_environment[i];

                let applied = apply(t, &self.substitutions);

                TypedExpression {
                    kind: ExprKind::Identifier(i),
                    ty: applied,
                }
            }
            ExprKind::Some(e) => {
                let inner = apply(&e.ty, &self.substitutions);

                TypedExpression {
                    kind: ExprKind::Some(e.clone()),
                    ty: Ty::App {
                        constructor: Box::new(Ty::Constructor(
                            "Option",
                            Kind::Pointer(Box::new(Kind::Star)),
                        )),
                        argument: Box::new(inner),
                    },
                }
            }
        }
    }
}

fn apply(ty: &Ty, sub: &Substitutions) -> Ty {
    match ty {
        Ty::TypeVariable(c) => {
            if let Some(replacement) = sub.get(c) {
                replacement.clone()
            } else {
                ty.clone()
            }
        }
        Ty::Fn { param, returns } => Ty::Fn {
            param: Box::new(apply(param, sub)),
            returns: Box::new(apply(returns, sub)),
        },
        Ty::App {
            constructor,
            argument,
        } => Ty::App {
            constructor: Box::new(apply(&constructor, sub)),
            argument: Box::new(apply(&argument, sub)),
        },
        x => x.clone(),
    }
}

fn unify(ty1: &Ty, ty2: &Ty, mut sub: Substitutions) -> Result<Substitutions, String> {
    let ty1 = apply(ty1, &sub);
    let ty2 = apply(ty2, &sub);

    if ty1 == ty2 {
        return Ok(sub);
    }

    match (ty1, ty2) {
        (Ty::TypeVariable(v), other) | (other, Ty::TypeVariable(v)) => {
            // if occurs_check(&Ty::TypeVariable(v), &other, &sub) {
            //     return Err(format!("Occurs check failed: '{}' vs '{}'", v, other));
            // }
            sub.insert(v, other);
            Ok(sub)
        }
        (
            Ty::Fn {
                param: p1,
                returns: r1,
            },
            Ty::Fn {
                param: p2,
                returns: r2,
            },
        ) => {
            let sub = unify(&*p1, &*p2, sub)?;
            unify(&*r1, &*r2, sub)
        }
        (
            Ty::App {
                constructor: c1,
                argument: a1,
            },
            Ty::App {
                constructor: c2,
                argument: a2,
            },
        ) => {
            let sub = unify(&*c1, &*c2, sub)?;
            unify(&*a1, &*a2, sub)
        }
        (Ty::ConcreteTy(ConcreteTy::I64), Ty::ConcreteTy(ConcreteTy::Integer)) =>{
            Ok(sub)
        }
        (Ty::ConcreteTy(ConcreteTy::I32), Ty::ConcreteTy(ConcreteTy::Integer)) =>{
            Ok(sub)
        }
        (t1, t2) => Err(format!("Cannot unify '{}' and '{}'", t1, t2)),
    }
}

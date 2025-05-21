use std::collections::HashMap;

use bumpalo::Bump;
pub use parser::parser as ast;
use parser::{Span, Spanned, parser::SpannedIdentifier};
pub mod infer;
pub struct HirLower<'src, 'hir> {
    next_id: usize,
    pub hir_map: HashMap<HirId, HirNode<'hir>>,
    pub def_map: HashMap<DefId, Definition<'src>>,

    pub expr_types: HashMap<HirId, TyKind>,
    pub constraints: Vec<(TyKind, TyKind)>,

    pub scopes: Vec<Scope<'src>>,
    pub arena: &'hir Bump,
}
#[derive(Debug)]
pub enum HirNode<'hir> {
    FunctionDefinition,
    Expression(&'hir Expression<'hir>),
}
#[derive(Debug)]
pub enum Definition<'src> {
    Function(FunctionDefinition<'src>),
    TypeParameter(SpannedIdentifier<'src>),
    Parameter(Parameter),
    Local(HirId),
}

#[derive(Debug, Default)]
pub struct Scope<'src> {
    pub names: HashMap<&'src str, DefId>,
}
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct HirId(usize);
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct DefId(usize);

impl<'src, 'hir> HirLower<'src, 'hir> {
    pub fn new(arena: &'hir bumpalo::Bump) -> Self {
        Self {
            scopes: vec![Scope {
                names: HashMap::new(),
            }],
            arena,
            def_map: HashMap::new(),
            hir_map: HashMap::new(),
            expr_types: HashMap::new(),
            constraints: vec![],
            next_id: 0,
        }
    }
    fn next_hir_id(&mut self) -> HirId {
        let id = self.next_id;
        self.next_id += 1;

        HirId(id)
    }
    fn next_ty_id(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;

        id
    }
    fn next_def_id(&mut self) -> DefId {
        let id = self.next_id;
        self.next_id += 1;

        DefId(id)
    }
    pub fn lower(&mut self, ast: &Spanned<ast::TranslationUnit<'src>>) {
        for item in &ast.0.items {
            self.lower_item(item);
        }
    }
    pub fn lower_item(&mut self, item: &Spanned<ast::Item<'src>>) {
        match &item.0 {
            ast::Item::Function {
                name,
                type_parameters,
                parameters,
                returns,
                body,
            } => self.lower_function_definition(name, type_parameters, parameters, returns, body),
            ast::Item::TypeDefinition {
                name,
                type_parameters,
                body,
            } => {}
        }
    }
    pub fn lower_function_definition(
        &mut self,
        name: &ast::SpannedIdentifier<'src>,
        type_parameters: &Spanned<Vec<Spanned<ast::TypeParameter<'src>>>>,
        parameters: &Spanned<Vec<Spanned<ast::Parameter<'src>>>>,
        return_ty: &Spanned<ast::Ty<'src>>,
        body: &Spanned<ast::Expression<'src>>,
    ) {
        let def_id = self.next_def_id();
        let mut hir_parameters = vec![];
        self.push_scope();
        for type_parameter in &type_parameters.0 {
            let id = self.next_def_id();
            self.def_map
                .insert(id, Definition::TypeParameter(type_parameter.0.name));
            self.scope().names.insert(type_parameter.0.name.0, id);
        }
        for parameter in &parameters.0 {
            let def_id = self.next_def_id();

            self.scope().names.insert(parameter.0.name.0, def_id);

            let ty = self.lower_ty(&parameter.0.ty);

            self.def_map.insert(
                def_id,
                Definition::Parameter(Parameter {
                    def_id,
                    ty,
                    span: parameter.1,
                }),
            );

            hir_parameters.push(def_id);
        }
        let body = self.lower_expression(body);
        self.def_map.insert(
            def_id,
            Definition::Function(FunctionDefinition {
                ident: *name,
                parameters: hir_parameters,
                body: body.id,
            }),
        );
        self.pop_scope();
    }
    pub fn lower_ty(&mut self, ty: &Spanned<ast::Ty<'src>>) -> Ty {
        let kind = match ty.0 {
            ast::Ty::Infer => TyKind::Unspecified(self.next_ty_id()),
            ast::Ty::I32 => TyKind::I32,
            ast::Ty::I64 => TyKind::I64,
            ast::Ty::Fn(_, _) => todo!(),
            ast::Ty::Name(name) => TyKind::Local(self.resolve_name(&name).unwrap()),
        };

        Ty { kind, span: ty.1 }
    }
    pub fn lower_expression(
        &mut self,
        expr: &Spanned<ast::Expression<'src>>,
    ) -> &'hir Expression<'hir> {
        let ty = TyKind::Unspecified(self.next_ty_id());
        let kind = match &expr.0 {
            ast::Expression::Path(i) => {
                let d = self
                    .resolve_name(i)
                    .expect(&format!("couldn't find name {}", i.0));
                dbg!(&self.def_map, d);
                match &self.def_map[&d] {
                    Definition::Function(function_definition) => todo!(),
                    Definition::TypeParameter(_) => {
                        todo!()
                    }
                    Definition::Parameter(parameter) => {
                        self.constraints
                            .push((ty.clone(), parameter.ty.kind.clone()));
                        // ty = parameter.ty.kind.clone();
                    }
                    Definition::Local(hir_id) => {
                        self.constraints
                            .push((ty.clone(), self.expr_types[hir_id].clone()));
                        // ty = self.expr_types[hir_id].clone();
                    }
                }
                ExprKind::Local(d)
            }
            ast::Expression::Block(items) => {
                self.push_scope();
                let block = items
                    .iter()
                    .map(|e| {
                        let x: &'hir Expression<'hir> = self.arena.alloc(self.lower_expression(e));
                        x
                    })
                    .collect::<Vec<_>>();
                self.pop_scope();
                if let Some(last_expr) = block.last() {
                    self.constraints
                        .push((ty.clone(), self.expr_types[&last_expr.id].clone()));
                    // ty = self.expr_types[&last_expr.id].clone();
                    // let t = match &self.hir_map[last_expr] {
                    //     HirNode::Expression(expression) => expression.ty.clone(),
                    //     _ => unreachable!(),
                    // };

                    // ty = t;
                }
                let x: &_ = self.arena.alloc_slice_fill_iter(block);
                ExprKind::Block(x)
            }
            ast::Expression::Let(binding, t, init) => {
                let def_id = self.next_def_id();
                if let Some(t) = t {
                    let explicit_ty = self.lower_ty(t).kind;
                    self.constraints.push((ty.clone(), explicit_ty));
                }
                let init = self.lower_expression(init);
                self.constraints.push((ty.clone(), self.expr_types[&init.id].clone()));

                self.scope().names.insert(binding.0, def_id);
                self.def_map.insert(def_id, Definition::Local(init.id));

                ExprKind::Let(self.arena.alloc(init))
            }
            ast::Expression::If {
                condition,
                then,
                elze,
            } => {
                let condition = self.lower_expression(&*condition);
                let then = self.lower_expression(&*then);
                let elze = self.lower_expression(&*elze);

                let lty = &self.expr_types[&then.id];
                let rty = &self.expr_types[&elze.id];

                self.constraints.push((lty.clone(), rty.clone()));

                ExprKind::If(
                    self.arena.alloc(condition),
                    self.arena.alloc(then),
                    self.arena.alloc(elze),
                )
            }
            ast::Expression::Add(l, r) => {
                let l = self.lower_expression(&*l);
                let r = self.lower_expression(&*r);

                let lty = &self.expr_types[&l.id];
                let rty = &self.expr_types[&r.id];

                self.constraints.push((lty.clone(), rty.clone()));
                self.constraints.push((ty.clone(), lty.clone()));
                self.constraints.push((ty.clone(), rty.clone()));

                ExprKind::Add(self.arena.alloc(l), self.arena.alloc(r))
            }
        };
        let id = self.next_hir_id();
        let e = self.arena.alloc(Expression {
            id,
            kind,
            span: expr.1,
        });

        self.hir_map.insert(id, HirNode::Expression(e));
        self.expr_types.insert(id, ty);

        e
    }
    pub fn resolve_name(&mut self, name: &SpannedIdentifier) -> Option<DefId> {
        for scope in self.scopes.iter().rev() {
            if let Some(def_id) = scope.names.get(name.0) {
                return Some(*def_id);
            }
        }
        None
    }
    fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }
    fn pop_scope(&mut self) {
        self.scopes.pop();
    }
    fn scope(&mut self) -> &mut Scope<'src> {
        self.scopes.last_mut().unwrap()
    }
    pub fn apply_substitutions(&mut self, sub: &Subs) {
        dbg!(&sub);
        let mut replace = vec![];
        for (id, ty) in &self.expr_types {
            match ty {
                TyKind::Unspecified(tid) => {
                    replace.push((*id, *tid));
                    // self.expr_types.insert(*id, sub[tid].clone());
                }
                _ => {}
            }
        }
        for (replace,tid) in replace {
            dbg!(&replace, tid);
            if let Some(replacment) = sub.get(&tid) {
                self.expr_types.insert(replace, replacment.clone());

            }
        }
    }
    pub fn create_substitutions(&mut self) -> Subs {
        let mut sub = HashMap::new();

        for (lhs, rhs) in &self.constraints {
            sub = Self::unify(lhs, rhs, sub).unwrap();
        }
        sub
    }
    fn apply(ty: &TyKind, sub: &Subs) -> TyKind {
        match ty {
            TyKind::Unspecified(c) => {
                if let Some(replacement) = sub.get(c) {
                    replacement.clone()
                } else {
                    ty.clone()
                }
            }
            x => x.clone(),
        }
    }
    fn unify(ty1: &TyKind, ty2: &TyKind, mut sub: Subs) -> Result<Subs, String> {
        let ty1 = Self::apply(ty1, &sub);
        let ty2 = Self::apply(ty2, &sub);

        if ty1 == ty2 {
            return Ok(sub);
        }

        match (ty1, ty2) {
            (TyKind::Unspecified(v), other) | (other, TyKind::Unspecified(v)) => {
                // if occurs_check(&Ty::TypeVariable(v), &other, &sub) {
                //     return Err(format!("Occurs check failed: '{}' vs '{}'", v, other));
                // }
                sub.insert(v, other);
                Ok(sub)
            }
            // (
            //     Ty::Fn {
            //         param: p1,
            //         returns: r1,
            //     },
            //     Ty::Fn {
            //         param: p2,
            //         returns: r2,
            //     },
            // ) => {
            //     let sub = unify(&*p1, &*p2, sub)?;
            //     unify(&*r1, &*r2, sub)
            // }
            // (
            //     Ty::App {
            //         constructor: c1,
            //         argument: a1,
            //     },
            //     Ty::App {
            //         constructor: c2,
            //         argument: a2,
            //     },
            // ) => {
            //     let sub = unify(&*c1, &*c2, sub)?;
            //     unify(&*a1, &*a2, sub)
            // }
            // (TyKind::I32(ConcreteTy::I64), TyKind::ConcreteTy(ConcreteTy::Integer)) => Ok(sub),
            // (Ty::ConcreteTy(ConcreteTy::I32), Ty::ConcreteTy(ConcreteTy::Integer)) => Ok(sub),
            (t1, t2) => Err(format!("Cannot unify '{:?}' and '{:?}'", t1, t2)),
        }
    }
}
type Subs = HashMap<usize, TyKind>;
#[derive(Debug)]
pub struct Ty {
    kind: TyKind,
    span: Span,
}
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TyKind {
    I32,
    I64,
    Unspecified(usize),
    Local(DefId),
}
#[derive(Debug)]
pub struct FunctionDefinition<'src> {
    ident: SpannedIdentifier<'src>,
    parameters: Vec<DefId>,
    body: HirId,
}
#[derive(Debug)]
pub struct Parameter {
    def_id: DefId,
    ty: Ty,
    span: Span,
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
    Add(&'hir Expression<'hir>, &'hir Expression<'hir>),
    Local(DefId),
}

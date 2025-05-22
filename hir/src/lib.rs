use std::{collections::HashMap, fmt::Display, ops::Deref, panic::UnwindSafe};

use bumpalo::Bump;
pub use parser::parser as ast;
use parser::{
    Span, Spanned,
    parser::{BinaryOperation, SpannedIdentifier, TypeDefinitionKind},
};
pub struct HirLower<'src, 'hir> {
    next_id: usize,
    pub hir_map: HashMap<HirId, HirNode<'hir>>,
    pub def_map: HashMap<DefId, Definition<'src>>,

    pub expr_types: HashMap<HirId, TyKind>,
    pub constraints: Vec<(TyKind, TyKind)>,

    pub scopes: Vec<Scope<'src>>,
    pub arena: &'hir Bump,
}
#[derive(Debug, Clone)]
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
    Z,
}

#[derive(Debug, Default)]
pub struct Scope<'src> {
    pub names: HashMap<&'src str, DefId>,
}
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct HirId(usize);
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
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
            } => self.lower_type_definition(name, type_parameters, body),
        }
    }
    pub fn lower_type_definition(
        &mut self,
        name: &ast::SpannedIdentifier<'src>,
        type_parameters: &Vec<Spanned<ast::TypeParameter<'src>>>,
        body: &Spanned<ast::TypeDefinitionKind<'src>>,
    ) {
        let id = self.next_def_id();
        self.def_map.insert(id, Definition::Z);

        self.scope().names.insert(name.0, id);
    }
    pub fn lower_function_definition(
        &mut self,
        name: &ast::SpannedIdentifier<'src>,
        type_parameters: &Vec<Spanned<ast::TypeParameter<'src>>>,
        parameters: &Spanned<Vec<Spanned<ast::Parameter<'src>>>>,
        return_ty: &Spanned<ast::Ty<'src>>,
        body: &Spanned<ast::Expression<'src>>,
    ) {
        let def_id = self.next_def_id();
        let mut hir_parameters = vec![];
        self.scope().names.insert(name.0, def_id);
        self.push_scope();
        for type_parameter in type_parameters {
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
        let body_ty = self.expr_types[&body.id].clone();
        let ret_ty = self.lower_ty(return_ty);
        self.constraints.push((ret_ty.kind.clone(), body_ty));

        self.def_map.insert(
            def_id,
            Definition::Function(FunctionDefinition {
                ident: *name,
                parameters: hir_parameters,
                body: body.id,
                ty: ret_ty
            }),
        );
        self.pop_scope();
        
    }
    pub fn lower_ty(&mut self, ty: &Spanned<ast::Ty<'src>>) -> Ty {
        let kind = match &ty.0 {
            ast::Ty::Infer => TyKind::Unspecified(self.next_ty_id()),
            ast::Ty::I32 => TyKind::I32,
            ast::Ty::I64 => TyKind::I64,
            ast::Ty::Fn(params, ret) => {
                let params = params.0.iter().map(|p| self.lower_ty(p)).collect();

                TyKind::Function(params, Box::new(self.lower_ty(ret.deref())))
            }
            ast::Ty::Name(name) => TyKind::Local(self.resolve_name(&name).unwrap()),
            ast::Ty::Apply(base, type_args) => TyKind::Apply(
                Box::new(self.lower_ty(base.deref())),
                type_args
                    .iter()
                    .map(|t| self.lower_ty(t))
                    .collect::<Vec<_>>(),
            ),
            ast::Ty::Bool => TyKind::Bool,
        };

        Ty { kind, span: ty.1 }
    }
    fn get_def_ty(&self, d: &DefId) -> TyKind {
        match &self.def_map[d] {
            Definition::Function(function_definition) => {
                
                let params = function_definition.parameters.iter().map(|p| Ty{ span: Span::from(0..0), kind: self.get_def_ty(p)}).collect::<Vec<_>>();

                TyKind::Function(params, Box::new(function_definition.ty.clone()))

                // let signature = TyKind::Function((), ())
                // function_definition.ty.kind.clone()
            },
            Definition::TypeParameter(_) => {
                todo!()
            }
            Definition::Parameter(parameter) => {
                parameter.ty.kind.clone()
                // self.constraints
                // .push((ty.clone(), parameter.ty.kind.clone()));
            }
            Definition::Local(hir_id) => {
                self.expr_types[hir_id].clone()
                // self.constraints
                //     .push((ty.clone(), self.expr_types[hir_id].clone()));
            }
            Definition::Z => todo!(),
        }
    }
    pub fn lower_expression(
        &mut self,
        expr: &Spanned<ast::Expression<'src>>,
    ) -> &'hir Expression<'hir> {
        let this_expression_ty = TyKind::Unspecified(self.next_ty_id());
        let kind = match &expr.0 {
            ast::Expression::Path(i) => {
                let d = self
                    .resolve_name(i)
                    .expect(&format!("couldn't find name {}", i.0));
                dbg!(&self.def_map, d);
                self.constraints.push((this_expression_ty.clone(), self.get_def_ty(&d)));
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
                        .push((this_expression_ty.clone(), self.expr_types[&last_expr.id].clone()));
                }
                let x: &_ = self.arena.alloc_slice_fill_iter(block);
                ExprKind::Block(x)
            }
            ast::Expression::Let(binding, t, init) => {
                let def_id = self.next_def_id();

                let init = self.lower_expression(init);
                let init_ty = self.expr_types[&init.id].clone();
                if let Some(t) = t {
                    let explicit_ty = self.lower_ty(t).kind;
                    // ensure init ty == explicit_ty
                    self.constraints.push((init_ty, explicit_ty));
                }
                // set our expr's tyvar = explicit_ty = init_ty
                self.constraints
                    .push((this_expression_ty.clone(), self.expr_types[&init.id].clone()));

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

                let cond_ty = &self.expr_types[&condition.id];

                let then_ty = &self.expr_types[&then.id];
                let elze_ty = &self.expr_types[&elze.id];

                self.constraints.push((cond_ty.clone(), TyKind::Bool));

                self.constraints.push((this_expression_ty.clone(), then_ty.clone()));
                self.constraints.push((this_expression_ty.clone(), elze_ty.clone()));

                ExprKind::If(
                    self.arena.alloc(condition),
                    self.arena.alloc(then),
                    self.arena.alloc(elze),
                )
            }
            ast::Expression::BinaryOperation(l, op, r) => {
                let l = self.lower_expression(&*l);
                let r = self.lower_expression(&*r);

                let lty = &self.expr_types[&l.id];
                let rty = &self.expr_types[&r.id];

                self.constraints.push((lty.clone(), rty.clone()));
                self.constraints.push((this_expression_ty.clone(), lty.clone()));
                self.constraints.push((this_expression_ty.clone(), rty.clone()));

                ExprKind::BinaryOperation(self.arena.alloc(l), op.clone(), self.arena.alloc(r))
            }
            ast::Expression::Some(inner) => {
                let x = self.resolve_name(&("Option", Span::from(0..0))).unwrap();

                let inner = self.lower_expression(&*inner);
                let inner_ty = self.expr_types[&inner.id].clone();

                let option = Ty {
                    kind: TyKind::Local(x),
                    span: Span::from(0..0),
                };
                let arg = Ty {
                    kind: inner_ty,
                    span: Span::from(0..0),
                };

                self.constraints
                    .push((this_expression_ty.clone(), TyKind::Apply(Box::new(option), vec![arg])));

                ExprKind::Some(inner)
            }
            ast::Expression::Literal(literal) => match literal {
                ast::Literal::Boolean(boolean_literal) => {
                    self.constraints.push((this_expression_ty.clone(), TyKind::Bool));
                    ExprKind::Literal(literal.clone())
                }
            },
            ast::Expression::Closure(parameters, returns, body) => {
                let mut parameter_tys = vec![];
                let mut parameter_definition = vec![];
                self.push_scope();
                for parameter in &parameters.0 {
                    let def_id = self.next_def_id();

                    self.scope().names.insert(parameter.0.name.0, def_id);

                    let ty = self.lower_ty(&parameter.0.ty);
                    parameter_tys.push(ty.clone());

                    self.def_map.insert(
                        def_id,
                        Definition::Parameter(Parameter {
                            def_id,
                            ty,
                            span: parameter.1,
                        }),
                    );
                    parameter_definition.push(def_id);
                }
                let body = self.lower_expression(body);
                let body_ty = self.expr_types[&body.id].clone();
                self.pop_scope();
                let ret = self.lower_ty(returns);
                self.constraints.push((body_ty.clone(), ret.kind.clone()));
                let func_ty = TyKind::Function(parameter_tys, Box::new(ret));
                self.constraints.push((this_expression_ty.clone(), func_ty.clone()));

                ExprKind::Closure(func_ty.clone(), body)
            }
            ast::Expression::Call(target, items) => {
                let target = self.lower_expression(target.deref());
                let target_ty = self.expr_types[&target.id].clone();

                let args = items
                    .iter()
                    .map(|a| self.lower_expression(a))
                    .collect::<Vec<_>>();
                let arg_tys = args
                    .iter()
                    .map(|e| Ty {
                        span: Span::from(0..0),
                        kind: self.expr_types[&e.id].clone(),
                    })
                    .collect::<Vec<_>>();

                let func_ty = TyKind::Function(
                    arg_tys,
                    Box::new(Ty {
                        span: Span::from(0..0),
                        kind: this_expression_ty.clone(),
                    }),
                );

                self.constraints.push((target_ty.clone(), func_ty));
                ExprKind::Call(target, self.arena.alloc_slice_fill_iter(args))
            }
            ast::Expression::X => todo!(),
        };
        let id = self.next_hir_id();
        let e = self.arena.alloc(Expression {
            id,
            kind,
            span: expr.1,
        });

        self.hir_map.insert(id, HirNode::Expression(e));
        self.expr_types.insert(id, this_expression_ty);

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
        // dbg!(&sub);
        let mut replace = vec![];
        for (id, ty) in &self.expr_types {
            match ty {
                TyKind::Unspecified(tid) => {
                    replace.push((*id, *tid));
                }
                _ => {}
            }
        }
        for (replace, tid) in replace {
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
            TyKind::Apply(base, args) => {
                let new_base = Ty {
                    kind: Self::apply(&base.kind, sub),
                    span: base.span,
                };

                let args = args
                    .iter()
                    .map(|arg| Ty {
                        kind: Self::apply(&arg.kind, sub),
                        span: arg.span,
                    })
                    .collect();

                TyKind::Apply(Box::new(new_base), args)
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
                sub.insert(v, other);
                Ok(sub)
            }
            (TyKind::Apply(left_base, left_args), TyKind::Apply(right_base, right_args)) => {
                if left_args.len() != right_args.len() {
                    return Err(format!(
                        "Cannot unify type applications with different argument counts: {:?} vs {:?}",
                        left_args, right_args
                    ));
                }

                // Ensure base is compatible
                sub = Self::unify(&left_base.kind, &right_base.kind, sub)?;
                // Ensure inner values are compatible
                for (left_arg, right_arg) in left_args.iter().zip(right_args.iter()) {
                    sub = Self::unify(&left_arg.kind, &right_arg.kind, sub)?;
                }

                Ok(sub)
            }
            (TyKind::Function(p1, r1), TyKind::Function(p2, r2)) => {
                for (left_param, right_param) in p1.iter().zip(p2.iter()) {
                    sub = Self::unify(&left_param.kind, &right_param.kind, sub)?;
                }
                sub = Self::unify(&r1.kind, &r2.kind, sub)?;

                Ok(sub)
            }
            (t1, t2) => Err(format!("Cannot unify '{:?}' and '{:?}'", t1, t2)),
        }
    }
}
type Subs = HashMap<usize, TyKind>;
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Ty {
    kind: TyKind,
    span: Span,
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
    ident: SpannedIdentifier<'src>,
    parameters: Vec<DefId>,
    body: HirId,
    ty: Ty
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
    BinaryOperation(
        &'hir Expression<'hir>,
        ast::BinaryOperation,
        &'hir Expression<'hir>,
    ),
    Local(DefId),
    Some(&'hir Expression<'hir>),
    Literal(ast::Literal),
    Closure(TyKind, &'hir Expression<'hir>),
    Call(&'hir Expression<'hir>, &'hir [&'hir Expression<'hir>]),
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

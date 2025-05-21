use std::collections::HashMap;

use crate::{Expression, HirLower, Ty};

type Substitutions = HashMap<usize, Ty>;

pub struct Inference<'src, 'hir> {
    pub type_var_counter: usize,
    pub constraints: Vec<(Ty, Ty)>,
    pub substitutions: Substitutions,
    pub type_environment: HashMap<&'static str, Ty>,
    ctx: HirLower<'src, 'hir>
}
impl<'src, 'hir> Inference<'src, 'hir> {
    pub fn new(ctx: HirLower<'src, 'hir>) -> Self {
        Self {
            type_var_counter: 0,
            constraints: vec![],
            substitutions: HashMap::new(),
            type_environment: HashMap::new(),
            ctx,
        }
    }
    // pub fn create_typed_expression_tree(&mut self, e: &Expression) -> Expression {
    //     match &e.kind {
    //         crate::ExprKind::Block(hir_ids) => todo!(),
    //         crate::ExprKind::Let(hir_id) => todo!(),
    //         crate::ExprKind::If(hir_id, hir_id1, hir_id2) => todo!(),
    //         crate::ExprKind::Local(def_id) => todo!(),
    //     }
    // }
}
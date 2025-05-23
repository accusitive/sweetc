use std::fmt::Write;

use ariadne::{Color, Label, Source};
use hir::{HirLower, ir::TyKind};
use parser::{lex, parse_string};
use yansi::Paint;

pub fn main() {
    let src = include_str!("../input/test.sw");
    let tokens = lex(src).unwrap();
    let ast = parse_string(&tokens, src).unwrap();
    dbg!(&ast);
    // println!("{}", ast.0);

    let arena = bumpalo::Bump::new();

    let mut lctx = HirLower::new(&arena);
    lctx.lower(&ast);
    debug_print_ast(true, src, &lctx);
    let subs = lctx.create_substitutions();
    lctx.apply_substitutions(&subs);
    debug_print_ast(false, src, &lctx);
}

fn debug_print_ast(before_inference: bool, src: &str, lctx: &HirLower) {
    let sorted = lctx.hir_map.clone();
    let mut x = sorted.iter().collect::<Vec<_>>();
    x.sort_by(|l, r| l.0.cmp(r.0));

    let mut labels = vec![];
    for (id, node) in x.iter() {
        let col = match labels.len() % 6 {
            0 => Color::Red,
            1 => Color::Green,
            2 => Color::Blue,
            3 => Color::Cyan,
            4 => Color::Magenta,
            5 => Color::Yellow,
            _ => Color::White,
        };
        match &node {
            hir::HirNode::Expression(expression) => {
                let expr_ty = lctx.expr_types[id].clone();
                // let pretty_name = |s: &TyKind| match s {
                //     TyKind::Local(def_id) => {
                //         match &lctx.def_map[&def_id]{
                //             hir::Definition::Function(function_definition) => todo!(),
                //             hir::Definition::Struct(struct_definition) => todo!(),
                //             hir::Definition::TypeParameter(_) => todo!(),
                //             hir::Definition::Parameter(parameter) => todo!(),
                //             hir::Definition::Local(hir_id) => todo!(),
                //             hir::Definition::ForwardType => todo!(),
                //         }
                //     },
                //     TyKind::Apply(base, args) => {
                //         format!("{}", pretty_name(&*base.kind))
                //     }
                //     _ => format!("{}", s),
                // };

                let constraints = lctx
                    .constraints
                    .iter()
                    .filter(|constraint| constraint.0 == expr_ty || constraint.1 == expr_ty)
                    .map(|cons| {
                        let relevant = match (cons.0 == expr_ty, cons.1 == expr_ty) {
                            (true, true) => todo!(),
                            (true, false) => format!("{}, ", cons.1),
                            (false, true) => format!("{}, ", cons.0),
                            (false, false) => todo!(),
                        };
                        relevant
                        // format!("{} == {}, ", cons.0, cons.1)
                    })
                    .collect::<String>();
                let t = match &lctx.expr_types[id] {
                    TyKind::Local(id) => {
                        match &lctx.def_map[id] {
                            hir::Definition::Function(function_definition) => todo!(),
                            hir::Definition::Struct(struct_definition) => todo!(),
                            hir::Definition::TypeParameter(i) => {
                                format!("{}", i)
                            }
                            hir::Definition::Parameter(parameter) => todo!(),
                            hir::Definition::Local(hir_id) => todo!(),
                            hir::Definition::ForwardType => todo!(),
                        }
                    }
                    tyk => format!("{}", tyk)
                };
                labels.push(
                    Label::new(("test.sw", expression.span.into_range()))
                        .with_message(
                            format!("ty: {} constraints: [{}]", t, constraints).paint(col),
                        )
                        .with_color(col),
                );
            }
            _ => {}
        }
    }
    ariadne::Report::build(
        ariadne::ReportKind::Custom(
            &format!("inferred: {}", !before_inference),
            ariadne::Color::Blue,
        ),
        ("test.sw", 0..0),
    )
    .with_labels(labels)
    .finish()
    .eprint(("test.sw", Source::from(src.to_string())))
    .unwrap();
}

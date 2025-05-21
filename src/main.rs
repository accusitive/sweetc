use ariadne::{Label, Source};
use hir::HirLower;
use parser::{lex, parse_string};

pub fn main() {
    let src = include_str!("../input/test.sw");
    let tokens = lex(src).unwrap();
    let ast = parse_string(&tokens, src).unwrap();
    dbg!(&ast);
    println!("{}", ast.0);

    let arena = bumpalo::Bump::new();

    let mut lctx = HirLower::new(&arena);
    lctx.lower(&ast);
    let subs = lctx.create_substitutions();
    lctx.apply_substitutions(&subs);

    for (id, node) in &lctx.hir_map {
        match &node {
            hir::HirNode::Expression(expression) => {
                ariadne::Report::build(
                    ariadne::ReportKind::Advice,
                    ("test", expression.span.into_range()),
                )
                .with_label(
                    Label::new(("test", expression.span.into_range())).with_message(format!("ty: {:?}", lctx.expr_types[id])),
                )
                .finish()
                .eprint(("test", Source::from(src.to_string())))
                .unwrap();
            }
            _ => {}
        }
    }

    let i = hir::infer::Inference::new(lctx);
}

pub fn main() {
    x()
}
#[derive(Debug, Clone)]
enum Effect {
    /// ×
    Compose(Box<Effect>, Box<Effect>),
    /// ⊥, aka None, Empty, Bottom
    Bottom,
    Fresh(RegionName, Units),
    Free(RegionName),
    Alloc(Units, RegionName),
    /// ⊔ (disjoint union)
    Union {
        t: Box<Effect>,
        f: Box<Effect>,
    },
    Effect(Box<Self>),
    // no clue if this is correct
    Recursive {
        latent: Box<Self>,
        effect: Box<Self>,
    },
    Arrow(Box<Self>)
}
type RegionName = String;
type Region = RegionName;
type Units = usize;
#[derive(Debug, Clone)]
enum Ty {
    TypeVariable(usize),
    Int,
    Unit,
    Bool,
    Ref(Box<Ty>), 
    Function(Box<TypeWithPlace>, Box<TypeWithPlace>),
    Forall(TypeSchema, Box<TypeWithPlace>, Box<TypeWithPlace>),
}
#[derive(Debug, Clone)]
struct TypeWithPlace {
    ty: Ty,
    region: Region,
}
#[derive(Debug, Clone)]
struct TypeSchema {
    ty_variable: char,
    region: Region,
    effect: Effect,
}
#[derive(Debug, Clone)]
struct ExpressionMeta {
    ty: Ty,
    region: Region,
    effect: Effect
}
fn x() {
    /*
    2 + 2
    */
    let r = RegionName::from("main");

    let fresh = Effect::Fresh(r.clone(), 0);
    
    let left = ExpressionMeta{
        ty: Ty::Int,
        region: r.clone(),
        effect: Effect::Bottom,
    };
    let right = ExpressionMeta{
        ty: Ty::Int,
        region: r.clone(),
        effect: Effect::Bottom,
    };
    let sum = ExpressionMeta{
        ty: Ty::Int,
        region: r.clone(),
        effect: Effect::Compose( Box::new(left.effect.clone()), Box::new(right.effect.clone()) ),
    };
    let free = Effect::Free(r.clone());

    let stack = Effect::Compose(Box::new(Effect::Compose(Box::new(free), Box::new(sum.effect.clone()))), Box::new(fresh));
    let block = ExpressionMeta {
        ty: sum.ty.clone(),
        region: r.clone(),
        effect: stack,
    };
    dbg!(&block);
}
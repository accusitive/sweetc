pub type Identifier = String;
#[derive(Debug, Clone)]
enum Type {
    Struct,
    Enum,
    Integer,
    Local(Identifier),
    /// De brujin index
    Generic(usize),
}
#[derive(Debug, Clone)]
enum Arity {
    Nullary,
    N(usize),
}
#[derive(Debug, Clone)]
enum TypeExpression {
    /// Introduction of new generics
    // fn identity<T>(x: T) -> T
    // technically, this works too: fn test(f: for<T> fn() -> T), but I dont know how to support that codegen wise
    Forall {
        // Empty, no data required in this minimal example. Generics use debrujin index, but I would stlil keep span/location data in a real compiler
        parameters: Vec<()>,
        ty: Box<Self>,
    },
    /// Type Constant when Arity::Nullary
    /// Type Function when Arity::N
    // int is considered a nullary constructor, no need to apply arguments to it
    Constructor(Type, Arity),
    /// Type Function Call
    // Option<T>
    // Option<C<T>> TypeApp(TypeCons(Option), TypeApp(C, T))
    Application {
        base: Box<Self>,
        arguments: Vec<Self>,
    },
    /// Expression Function
    // fn(int) -> int
    Function {
        parameters: Vec<Self>,
        ret: Box<Self>,
    },
    
}

#[test]
fn test() {
    // fn add(x: int, y: int) -> int
    {
        let int = TypeExpression::Constructor(Type::Integer, Arity::Nullary);
        let func = TypeExpression::Function {
            parameters: vec![int.clone(), int.clone()],
            ret: Box::new(int.clone()),
        };
    }

    // fn test() -> C<int>
    {
        let int = TypeExpression::Constructor(Type::Integer, Arity::Nullary);
        let container = TypeExpression::Constructor(Type::Generic(0), Arity::N(1));
        let applied = TypeExpression::Application {
            base: Box::new(container),
            arguments: vec![int.clone()],
        };
        let func = TypeExpression::Function {
            parameters: vec![],
            ret: Box::new(applied),
        };
    }

    // fn identity<T>(x: T) -> T
    {
        let t = TypeExpression::Constructor(Type::Generic(0), Arity::Nullary);
        let forall = TypeExpression::Forall {
            parameters: vec![()],
            ty: Box::new(TypeExpression::Function {
                parameters: vec![t.clone()],
                ret: Box::new(t.clone()),
            }),
        };
    }

    // fn dual_identity<T, U>(x: T, y: U) -> Either<T, U>
    {
        let t = TypeExpression::Constructor(Type::Generic(1), Arity::Nullary);
        let u = TypeExpression::Constructor(Type::Generic(0), Arity::Nullary);

        let either = TypeExpression::Constructor(Type::Local("Either".to_string()), Arity::N(2));
        let either_tu = TypeExpression::Application {
            base: Box::new(either),
            arguments: vec![t.clone(), u.clone()],
        };

        let forall = TypeExpression::Forall {
            parameters: vec![(), ()],
            ty: Box::new(TypeExpression::Function {
                parameters: vec![t.clone(), u.clone()],
                ret: Box::new(either_tu),
            }),
        };
    }
}

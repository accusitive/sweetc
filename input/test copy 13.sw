type Option<T> {
    | Some(T)
    | None
}
type FunctorSum<F<?>, G<?>, A> {
    | InL(F<A>)
    | InR(G<A>)
}
// typeclass `Monad` takes 1 type parameter, that itself takes 1 type parameter (HKT)
class Monad<M<?>> {
    fn unit<T>   : (this: T) -> M<T>
    fn bind<A, B>: (this: M<A>, func: fn(A) -> M<B>) -> M<B>
}
class Functor<F<?>> {
    fn map<A, B> : (this: F<A>, func: fn(A) -> B) -> F<B>
}
// Provide implementation of Monad<M>::unit and Monad<M>::bind where M = Option
impl Monad<Option> {
    // also called return. no preference for what this should be called honestly
    fn unit<T>: (this: T) -> Option<T> {
        Option::Some(this)
    }
    fn bind<A, B>: (this: Option<A>, func: fn(A) -> Option<B>) -> Option<B> {
        match this {
            | Some(inner) => func(inner)
            | None => None
        }
    }
}
impl Functor<Option> {
    fn map<A, B>: (this: Option<A>, func: fn(A) -> B) -> Option<B> {
        match this {
            | Some(inner) => Monad<Option<B>>::unit(func(inner))
            | None => Option<B>::None
        }
    }
}
type SinglyLinkedList<T> {
    | Value(T, SinglyLinkedList<T>)
    | Empty
}
// T = Item 
// I = Iterator
class Iterator<I, T> {
    fn next: (iter: I) -> Option<(T, I)>
}

impl<T> Iterator<SinglyLinkedList<T>, T> {
    fn next: (this: SinglyLinkedList<T>) -> Option<(T, SinglyLinkedList<T>)> {
        match this {
            | Value(item, remainder) => Some((item, remainder))
            | Empty => None
        }
    }
}
// Option is an iterator that always yields one item
impl<T> Iterator<Option<T>, T> {
    // alias Self: Option<T>

    fn next: (this: Self) -> Option<(T, Self)> {
        match this {
            | Some(inner) => Some((item, None))
            | None => None
        }
    }
}

fn unwrap<T>: (value: Option<T>) -> T {
    match value {
        | Some(inner) => inner
        | None => __rt__panic() 
    }
}

class Simple<T> {
    // note: `this` is not a keyword or anything, just a naming convention. could easily be `value`. havent decided on idioms
    fn nop: (this: T) -> T
}
class OtherSimple<T> {
    fn no: (this: T) -> ()
}
class Third<T> {

}
impl<T> Simple<T> {
    fn nop: (this: T) -> T {
        this
    }
}
// implement Simple for any type T where an implementation of Third<T> exists
impl<T> where(impl Third<T>) Simple<T> {
    // ..
}
// use go takes 1 type parameter, `S`
// S is valid for any type where an implemention Simple<S> exists AND no implementation for OtherSimple<S> exists
fn constraint_example<S> where(impl Simple<S>, !impl OtherSimple<S>): (simple: S) -> Option<S> {
    Option::Some(simple) |> Simple<S>::nop
}

type ConstraintedType<T> where(impl Simple<T>) {
    value: T
}
fn use_list: () -> void {
    let list = SinglyLinkedList::Value(ZERO, SinglyLinkedList::Value(ONE, SinglyLinkedList::Value(TWO, SinglyLinkedList::Empty)))
    // use explicit types here, hopefully they could be inferred
    let (list, element) = 
        list
        |> Iterator<_>::next
        |> Option<_>::unwrap
    assert(element == 0);
    let (list, element) = list |> Iterator::next |> Option::unwrap
    assert(element == 1);
    let (list, element) = list.next().unwrap()
    assert(element == 2);
}
fn int_tuple_to_float_pos: (test: (i32, i32)) -> Position<f32> {
    // note: this is a showcase on how you can use pipelines on functions that take more than 1 argument by using a closure, see above for simpler case
    let p = test 
            |> |t| into_pos(t.0, t.1) 
            |> |p| (into_float(p.x), into_float(p.y)) 
            |> |p| into_pos(p.0, .1) 
    p
}
// Showcase using a monad
fn main: () -> void {
    let plus_one        = fn(x: i32) -> i32         { x + 1 }
    let plus_one_option = fn(x: i32) -> Option<i32> { Some(plus_one(x)) }
    let value = Some(1)
    {
        let result = Option::bind(value, plus_one_option)
        let result_2 = Option::map(result, plus_one)
        print(result_2)
    }
}

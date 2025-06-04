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
    | None
}
// T = Item 
// I = Iterator
class Iterator<I, T> {
    fn next: (iter: I) -> Option<(T, I)>;
}

impl<T> Iterator<SinglyLinkedList<T>, T> {
    fn next: (this: SinglyLinkedList<T>) -> Option<(T, SinglyLinkedList<T>)> {
        match this {
            | Value(item, remainder) => Some((item, remainder))
            | None => None
        }
    }
}
// Option is an iterator that always yields one item
impl<T> Iterator<Option<T>, T> {
    alias Self: Option<T>

    fn next: (this: Self) -> Option<(T, Self)> {
        match this {
            | Value(item) => Some((item, None))
            | None => None
        }
    }
}

fn unwrap<T>: (value: Option<T>) -> T {
    match value {
        | Some(inner) -> inner
        | None -> __rt__panic() 
    }
}

fn use_list: () -> void {
    let list = SinglyLinkedList::Value(0, SinglyLinkedList::Value(1, SinglyLinkedList::Value(2, SinglyLinkedList::None)))
    // use explicit types here, hopefully they could be inferred
    let (list, element) = list.next().unwrap()
    assert(element == 0);
    let (list, element) = list.next().unwrap()
    assert(element == 1);
    let (list, element) = list.next().unwrap()
    assert(element == 2);
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
    // or, alternatively
    {
        let result = Option::bind(value, plus_one_option)
        let result_2 = result.map(plus_one)
        print(result_2)
    }
}

type Option<T> {
    | Some(T)
    | None
}
type NonZeroInt where(i: Int) i > 0
type AlwaysSome<T> where(o: Option<T>) o.is_some()

fn use() -> void {
    let n = new Option::None;
    let always_some = match n {
        | Option::Some(s) -> Option::Some(s)
        | Option::None -> panic() // panic -> void, void can be coerced into any type since its never actually reached/produced. think rust's never type
    };

    {}
}
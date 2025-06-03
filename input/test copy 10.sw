type Option<T> {
    value: T
}
type Result<T, E> {
    value: T,
    value2: E
}
fn identity<T>(x: T) -> T {
    x
}
fn wrap<T, U>(v: T, control: bool, t: fn(T) -> U, f: fn(T) -> U) -> Option<U> {
    let z = identity(v);
    let value = new Option::Some(t(v));

    value
}
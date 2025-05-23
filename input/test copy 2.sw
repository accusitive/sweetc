type Option<T> {
    value: T
}
type Result<T, E> {
    value: T,
    value2: E
}
fn nop<T>(x: T) -> T {
    x
}
fn wrap<T, U>(v: T, control: bool, t: fn(T) -> U, f: fn(T) -> U) -> Option<U> {
    let z = nop(v);
    let value: Option<_> = if control {
        some t(v)
    } else {
        some f(v)
    };

    value
}
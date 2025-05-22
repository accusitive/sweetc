type Option<T> {
    value: T
}

fn wrap<T, U>(v: T, control: bool, t: fn(T) -> U, f: fn(T) -> U) -> Option<U> {
    if control {
        some t<_>(v)
    } else {
        some f<_>(v)
    }
}
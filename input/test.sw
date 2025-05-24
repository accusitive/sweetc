type Option<T> {
    Some(T) | None
}

fn make_some<T>(val: T) -> Option<T> {
    Option::Some(val)
}

fn get_hkt<C<?>, T>(container: C, get: fn(C, u64) -> T, index: u64, rewrap: fn(T) -> C<T>) -> C<T> {
    
    let value = get(container, index) // automatically inferred to be T
    let wrapped = rewrap(value) // inferred to be C<T>

    

    wrapped
}
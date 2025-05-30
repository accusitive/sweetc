fn enwrap<W<?>, T>(value: Option<T>, wrap: fn(T) -> W<T>) -> Option<W<T>> {
    //match value {
    //    | Some(val) -> Some(wrap(val))
    //    | None -> None
    //}
}

fn enwrap(value: Option<T>, wrap: fn(T) -> W<T>) -> Option<W<T>> {
    let a = b;
    let b = c;
    map(value, wrap)
}
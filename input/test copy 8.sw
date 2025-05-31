fn test() -> int {
    {}
}
fn identity <T> (x: T) -> T {
    x
}
fn fidentity <T> (x: fn() -> T) -> T {
    x()
}
fn uses_ranked(x: for<T> fn() -> Option<T>) -> void {
    let _i32bit = match x<i32>() {
        | Some(v) -> true
        | None -> false
    }
    let _64bit = match x<i64>() {
        | Some(v) -> true
        | None -> false
    }
    false
}
fn make_none<T>() -> Option<T> {
    Option::None
}
fn use() -> void {
    uses_ranked(make_none)
}
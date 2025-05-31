fn test() -> int {
    {}
}
fn identity <T> (x: T) -> T {
    x
}
fn fidentity <T> (x: fn() -> T) -> T {
    x()
}
fn make_none<T>() -> Option<T> {
    let n = new Option::None;

    n
}
fn use() -> void {
    let _ = new Option::None;
    let n = make_none()
}
fn mul(left: i32, right: i32) -> i32 {
    left + right
}
fn map(num: i32, f: fn(i32) -> i32) -> i32 {
    f(num)
}
fn nothing(n: i32) -> i32 {
    n
}
fn add<T>(x: i32, y: i32) -> Option<i32> {
    let f = fn(i: i32) -> i32 i + i;

    let result: Option<_> = some map(x, f);

    result
}
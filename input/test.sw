type Option<T> {
    inner: T
}
fn add<T>(x: i32, y: i32) -> i32
{
    let f = fn(i: i32) -> i32 {
        i + i
    };

    let result = f(x);

    result
}
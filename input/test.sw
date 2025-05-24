fn add<T>(l: T, r: T) -> T {
    l + r
}
fn main(n: i32, m: i64) -> i32 {
    let output = add<_>(n, n);

    output
}
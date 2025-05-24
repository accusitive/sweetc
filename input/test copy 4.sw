type Option<T> {
    | Some(T)
    | None
}
type TwoOptions<T, U> {
    first: Option<T>,
    second: Option<U>
}
fn macro_example(opt_value: i32) -> Option<i32> {
    Option::Some(opt_value)
}
fn enclose<W<?>, V>(value: V) -> W<V> {
    Enclose<W<V>>::enclose(v)
}

fn add<T>(l: T, r: T) -> T {
    l + r
}

fn main(n: i32, m: i64) -> Wrapper<i64> {
    let output_i32 = add(n, n): i32;
    let output_i64 = add(m, m): i64;
    let sum = output_i32: i32 + output_i64: i64: bool;

    Enclose<Wrapper>::enclose(sum)
}
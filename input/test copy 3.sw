// Implement for any W that:
// - takes 1 type parameter
// - implements Enclose
fn enclose<W<?>: + Enclose<W>, V>(value: V) -> W<V> {
    Enclose<W>::enclose(v)
}

class Enclose<W<?>> {
    fn enclose<v: V>(val: V) -> W<V>;
}

struct Wrapper<T> {
    value: T
}

impl Enclose<Wrapper> {
    fn enclose<v: V>(val: V) -> Wrapper<V> {
        new Wrapper {
            value: val
        }
    }
}

fn add<T>(l: T, r: T) -> T {
    l + r
}

fn main(n: i32, m: i64) -> Wrapper<i64> {
    let output_i32 = add(n, n);
    let output_i64 = add(m, m);
    let sum = (output_i32 as i64) + (output_i64);

    Enclose<Wrapper>::enclose(sum)
}
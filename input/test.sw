type Vec2<T> {
    x: i32,
    y: T
}
//fn identity<T>(x: T) -> i32 {
//    let y: i32 = x;
//    y + y
//}

fn add<T>(x: T, y: T) -> T {
    let result = x + y;

    let intermediate = result;

    intermediate
}
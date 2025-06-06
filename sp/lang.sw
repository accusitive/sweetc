fn main: () -> void {
    let reg = newrgn; // unbounded region

    let x = 0 at reg;
    let f = || loc(x);
    freergn reg;

    let new_x = f();
}
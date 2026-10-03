fn main() {
    let mut x: (&u32,) = (&1,);
    let mut y: (&u32,) = (&2,);
    let mut z = 3;
    y.0 = x.0;
    x.0 = &z;
    z += 1;
    dbg!(y.0);
}

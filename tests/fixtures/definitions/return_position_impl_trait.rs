trait T {
    fn a() -> impl Copy;
    fn b() -> impl Copy;
}

impl T for () {
    fn a() -> impl Copy {
        1_u8
    }

    fn b() -> impl Copy {
        2_u8
    }
}

fn main() {}

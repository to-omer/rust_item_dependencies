trait Bounds {
    fn maximum() -> Self;
    fn minimum() -> Self;
}

macro_rules! impl_bounds {
    ($($primitive:ident)*) => {
        $(
            impl Bounds for $primitive {
                fn maximum() -> Self {
                    $primitive::MAX
                }

                fn minimum() -> Self {
                    $primitive::MIN
                }
            }
        )*
    };
}

impl_bounds!(i64 u64);

fn main() {
    assert_eq!(i64::maximum(), i64::MAX);
}

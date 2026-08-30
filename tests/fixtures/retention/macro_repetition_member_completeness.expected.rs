trait Bounds {
    fn maximum() -> Self;

}

macro_rules! impl_bounds {
    ($($primitive:ident)*) => {
        $(
            impl Bounds for $primitive {
                fn maximum() -> Self {
                    $primitive::MAX
                }


            }
        )*
    };
}

impl_bounds!(i64 );

fn main() {
    assert_eq!(i64::maximum(), i64::MAX);
}

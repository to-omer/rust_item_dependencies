

trait One {
    fn one() -> Self;
}

macro_rules! implement {
($({$(<$T:ident:$Bound:ident>)? $Trait:ident $method:ident $($ty:ty)*, $value:expr})*) => {
    $(implement!(@impl [] $Trait $method [$($ty)*], $value);)*
};

(@impl [] $Trait:ident $method:ident [$($ty:ty)*], $value:expr) => {
    $(impl $Trait for $ty { fn $method() -> Self { $value } })*
};
}

implement!(
{One one u8, 1}

);

fn main() {
    assert_eq!(u8::one(), 1);
}

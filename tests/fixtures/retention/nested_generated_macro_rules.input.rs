trait Zero {
    fn zero() -> Self;
}

trait One {
    fn one() -> Self;
}

macro_rules! implement {
($({$(<$T:ident:$Bound:ident>)? $Trait:ident $method:ident $($ty:ty)*, $value:expr})*) => {
    $(implement!(@impl [$(<$T:$Bound>)?] $Trait $method [$($ty)*], $value);)*
};
(@impl [<$T:ident:$Bound:ident>] $Trait:ident $method:ident [$($ty:ty)*], $value:expr) => {
    $(impl<$T: $Bound> $Trait for $ty { fn $method() -> Self { $value } })*
};
(@impl [] $Trait:ident $method:ident [$($ty:ty)*], $value:expr) => {
    $(impl $Trait for $ty { fn $method() -> Self { $value } })*
};
}

implement!(
{Zero zero u8, 0}
{One one u8, 1}
{<T:Zero> Zero zero std::num::Wrapping<T>, Self(T::zero())}
);

fn main() {
    assert_eq!(u8::one(), 1);
}

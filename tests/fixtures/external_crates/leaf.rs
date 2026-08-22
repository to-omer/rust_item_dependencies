use std::ops::Add;

pub fn leaf_value() -> i32 {
    4
}

pub fn double<T>(value: T) -> T
where
    T: Add<Output = T> + Copy,
{
    value + value
}

pub trait Measure {
    fn measure(&self) -> i32;
}

pub struct Number(pub i32);

impl Measure for Number {
    fn measure(&self) -> i32 {
        self.0
    }
}

use core::ops::{Add, Index};

struct Number(u8);

impl Add for Number {
    type Output = Number;

    fn add(self, rhs: Number) -> Number {
        Number(self.0 + rhs.0)
    }
}

struct Values([u8; 1]);

impl Index<usize> for Values {
    type Output = u8;

    fn index(&self, index: usize) -> &u8 {
        &self.0[index]
    }
}

fn call<F: Fn(u8) -> u8>(function: F) -> u8 {
    function(1)
}

fn main() {
    let _ = Number(1) + Number(2);
    let _ = Values([3])[0];
    let _ = call(|value| value);
}

extern crate external_wrapper as wrapper;

use wrapper::{Measure, Number};

fn local_dead_item() -> i32 {
    99
}

fn main() {
    let number = Number(5);
    let total = wrapper::external_function()
        + wrapper::external_generic(3_i32)
        + number.measure()
        + wrapper::external_macro!(1_i32);
    println!("{total}");
}

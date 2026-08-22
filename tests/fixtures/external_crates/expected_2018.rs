use external_wrapper as wrapper;
use wrapper::{Measure, Number};



fn main() {
    let number = Number(5);
    let total = wrapper::external_function()
        + wrapper::external_generic(3_i32)
        + number.measure()
        + wrapper::external_macro!(1_i32);
    println!("{total}");
}

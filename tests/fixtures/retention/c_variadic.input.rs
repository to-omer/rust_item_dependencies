use std::ffi::VaList;

unsafe extern "C" fn sum(count: u32, args: ...) -> i32 {
    unsafe { consume(count, args) }
}

unsafe fn consume(count: u32, mut args: VaList<'_>) -> i32 {
    let mut total = 0;
    for _ in 0..count {
        total += unsafe { args.next_arg::<i32>() };
    }
    total
}

fn unused() -> i32 {
    99
}

fn main() {
    let sum_fn: unsafe extern "C" fn(u32, ...) -> i32 = sum;
    println!("{}", unsafe { sum_fn(3, 10i32, 20i32, 12i32) });
}

unsafe extern "C" fn sum(count: u32, mut args: ...) -> i32 {
    let mut total = 0;
    for _ in 0..count {
        total += unsafe { args.next_arg::<i32>() };
    }
    total
}

#[cfg(target_arch = "aarch64")]
#[unsafe(naked)]
unsafe extern "C" fn naked_sum(_: u32, _: ...) -> i32 {
    core::arch::naked_asm!("b {}", sym sum);
}

#[cfg(target_arch = "x86_64")]
#[unsafe(naked)]
unsafe extern "C" fn naked_sum(_: u32, _: ...) -> i32 {
    core::arch::naked_asm!("jmp {}", sym sum);
}

fn unused() -> i32 {
    99
}

fn main() {
    println!("{}", unsafe { naked_sum(3, 10i32, 20i32, 12i32) });
}

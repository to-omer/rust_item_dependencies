extern crate alloc;

use std::collections::VecDeque;

fn round_trip() -> Vec<i32> {
    let (ptr, len, capacity) = vec![99, 10, 20, 12].into_parts();
    unsafe { Vec::from_parts(ptr, len, capacity) }
}

fn unused() -> i32 {
    99
}

fn main() {
    let ptr = Box::into_non_null(Box::new(round_trip()));
    let values = unsafe { Box::from_non_null(ptr) };
    let mut queue: VecDeque<i32> = VecDeque::from(*values);
    queue.retain_back(3);
    let slice = queue.make_contiguous();
    let raw = slice as *const [i32];
    let layout = unsafe { std::alloc::Layout::for_value_raw(raw) };
    assert_eq!(layout.size(), unsafe { std::mem::size_of_val_raw(raw) });
    assert_eq!(layout.align(), unsafe { std::mem::align_of_val_raw(raw) });
    assert_eq!(Box::new([10, 20, 12]).into_iter().sum::<i32>(), 42);
    assert_eq!(
        String::from_utf8(vec![0xff]).unwrap_err().into_utf8_lossy(),
        "\u{fffd}"
    );
    let mut buffer = std::fmt::NumBuffer::new();
    assert_eq!(42u32.format_into(&mut buffer), "42");
    let mut buffer = alloc::fmt::NumBuffer::new();
    assert_eq!((-42i32).format_into(&mut buffer), "-42");
    let label = String::from_utf8_lossy_owned(vec![b'o', b'k']);
    println!("{label}:{}", queue.iter().sum::<i32>());
}

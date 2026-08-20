struct S {
    a: u8,
}

fn main() {
    let _ = std::mem::offset_of!(S, a);
}

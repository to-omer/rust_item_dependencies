macro_rules! field_type {
    () => {
        u8
    };
}

macro_rules! value {
    () => {
        1_u8
    };
}

struct Holder {
    field: field_type!(),
}

struct Generic<T = field_type!()> {
    value: T,
}

fn capture() {
    let closure = || value!();
    let _ = closure();
}

const INLINE: u8 = const { value!() };

fn main() {}

fn type_target<T>(_: T) {}

fn type_caller<U>(value: U) {
    type_target(value);
}

fn const_target<const N: usize>(_: [u8; N]) {}

fn const_caller<const M: usize>(value: [u8; M]) {
    const_target(value);
}

fn main() {}

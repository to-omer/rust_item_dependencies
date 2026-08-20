macro_rules! make_generated {
    () => {
        fn generated() -> usize {
            1
        }
    };
}

make_generated!();

trait Value {
    fn value(&self) -> usize;
}

struct Kept;

impl Value for Kept {
    fn value(&self) -> usize {
        generated()
    }
}

struct AlsoKept;

impl Value for AlsoKept {
    fn value(&self) -> usize {
        generated() + 1
    }
}

fn call<T: Value>(value: T) -> usize {
    value.value()
}

fn unused() -> usize {
    99
}

fn main() {
    println!("{}", call(Kept) + call(AlsoKept));
}

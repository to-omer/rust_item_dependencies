#![allow(dead_code)]

#[inline(never)]
fn concrete<T>() {
    std::hint::black_box(std::mem::size_of::<T>());
}

fn from_const() {}
fn kept_first() {}
fn kept_second() {}
fn unseeded() {}
fn mentioned_call() {}
fn mentioned_pointer() {}

const TABLE: [fn(); 1] = [from_const];

#[used]
static KEEP: [fn(); 2] = [kept_first, kept_second];

static ORDINARY: [fn(); 1] = [unseeded];

trait Parent {
    fn inherited(&self) -> u8 {
        1
    }
}

trait Object: Parent {
    type Item;

    fn selected(&self) -> u8;
}

struct Value;

impl Drop for Value {
    fn drop(&mut self) {}
}

impl Parent for Value {}

impl Object for Value {
    type Item = u8;

    fn selected(&self) -> u8 {
        2
    }
}

trait Dispatch<T> {
    fn invoke(&self) -> usize {
        std::mem::size_of::<T>()
    }
}

struct Defaulted;

impl Dispatch<u16> for Defaulted {}

struct Overridden;

impl Dispatch<u32> for Overridden {
    fn invoke(&self) -> usize {
        std::mem::size_of::<u32>() + 1
    }
}

#[inline(never)]
fn dependencies() {
    concrete::<u8>();
    concrete::<u8>();
    concrete::<u16>();
    std::hint::black_box(TABLE);

    let defaulted = Defaulted;
    std::hint::black_box(Dispatch::<u16>::invoke(&defaulted));

    let overridden = Overridden;
    std::hint::black_box(Dispatch::<u32>::invoke(&overridden));

    {
        let first = Value;
        let object: &(dyn Object<Item = u8> + Send) = &first;
        std::hint::black_box(object.inherited());
        std::hint::black_box(object.selected());
    }

    {
        let second = Value;
        std::hint::black_box(&second);
    }

    if false {
        mentioned_call();
        let pointer: fn() = mentioned_pointer;
        std::hint::black_box(pointer);
    }
}

fn main() {
    dependencies();
}

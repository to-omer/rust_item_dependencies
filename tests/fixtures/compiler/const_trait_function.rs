#![allow(dead_code)]

trait Table<A, const K: usize> {
    fn make();

    const FUNCTIONS: [fn(); 1] = [Self::make];
}

struct Defaulted;

impl Table<u16, 3> for Defaulted {
    fn make() {}
}

struct Overridden;

impl Table<u32, 5> for Overridden {
    fn make() {}

    const FUNCTIONS: [fn(); 1] = [<Self as Table<u32, 5>>::make];
}

struct MultiSite;

impl Table<u8, 2> for MultiSite {
    fn make() {}
}

struct Unused;

impl Table<u64, 7> for Unused {
    fn make() {}

    const FUNCTIONS: [fn(); 1] = [Self::make];
}

trait Tracked {
    #[track_caller]
    fn call();

    const FUNCTION: fn() = Self::call;
}

struct TrackedImpl;

impl Tracked for TrackedImpl {
    #[track_caller]
    fn call() {}
}

#[inline(never)]
fn from_inline_const<T: Table<A, K>, A, const K: usize>() -> fn() {
    const { <T as Table<A, K>>::FUNCTIONS[0] }
}

#[inline(never)]
fn tracked_pointer<T: Tracked>() -> fn() {
    const { <T as Tracked>::FUNCTION }
}

#[inline(never)]
fn from_two_sites<T: Table<A, K>, A, const K: usize>() -> (fn(), fn()) {
    const {
        (
            <T as Table<A, K>>::FUNCTIONS[0],
            <T as Table<A, K>>::FUNCTIONS[0],
        )
    }
}

#[inline(never)]
fn from_promoted<T: Table<A, K>, A, const K: usize>() -> &'static [(fn(), usize); 1] {
    &[(<T as Table<A, K>>::make, std::mem::size_of::<u8>())]
}

fn main() {
    std::hint::black_box(from_inline_const::<Defaulted, u16, 3>());
    std::hint::black_box(from_inline_const::<Overridden, u32, 5>());
    std::hint::black_box(from_promoted::<Defaulted, u16, 3>());
    std::hint::black_box(tracked_pointer::<TrackedImpl>());
    std::hint::black_box(from_two_sites::<MultiSite, u8, 2>());
}

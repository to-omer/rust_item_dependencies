#![allow(dead_code)]

trait Marker {}

trait Super {
    fn inherited(&self) -> u8 {
        1
    }
}

trait Object: Super + Marker {
    type Value;

    fn selected(&self) -> u8;
}

struct Concrete;

impl Marker for Concrete {}

impl Super for Concrete {}

impl Object for Concrete {
    type Value = u8;

    fn selected(&self) -> u8 {
        2
    }
}

trait LifetimeMarker<'a, T> {}

trait HrtbValue {
    type Output;
}

trait HrtbDispatch: HrtbValue + for<'a> LifetimeMarker<'a, Self::Output> {
    fn invoke_hrtb(&self) {}
}

struct LifetimeRouted;

impl HrtbValue for LifetimeRouted {
    type Output = u16;
}

impl<'a> LifetimeMarker<'a, u16> for LifetimeRouted {}

impl HrtbDispatch for LifetimeRouted {}

trait Dispatch<A, const K: usize>: Marker {
    fn invoke(&self) -> usize {
        std::mem::size_of::<A>() + K
    }
}

struct Routed;

impl Marker for Routed {}

impl Dispatch<u16, 3> for Routed {}

struct UnusedRoute;

impl Marker for UnusedRoute {}

impl Dispatch<u32, 9> for UnusedRoute {}

#[inline(never)]
fn proof_owner() {
    let routed = Routed;
    std::hint::black_box(Dispatch::<u16, 3>::invoke(&routed));

    let lifetime_routed = LifetimeRouted;
    HrtbDispatch::invoke_hrtb(&lifetime_routed);

    let concrete = Concrete;
    let object: &(dyn Object<Value = u8> + Send) = &concrete;
    std::hint::black_box(object.selected());
    std::hint::black_box(object.inherited());
}

fn main() {
    proof_owner();
}

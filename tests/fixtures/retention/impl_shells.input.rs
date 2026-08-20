struct Used;

impl Used {
    fn unused(&self) {}
}

unsafe trait Marker {}

unsafe impl Marker for Used {}

fn main() {
    let value = Used;
    let _: &dyn Marker = &value;
}

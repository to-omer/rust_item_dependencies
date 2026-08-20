struct Used;



unsafe trait Marker {}

unsafe impl Marker for Used {}

fn main() {
    let value = Used;
    let _: &dyn Marker = &value;
}

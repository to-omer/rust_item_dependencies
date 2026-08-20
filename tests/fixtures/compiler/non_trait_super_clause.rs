trait Base {
    type Item;
}

trait WithProjection: Base<Item = u8> {
    fn invoke(&self) {}
}

struct Concrete;

impl Base for Concrete {
    type Item = u8;
}

impl WithProjection for Concrete {}

fn main() {
    WithProjection::invoke(&Concrete);

    let object: &dyn WithProjection = &Concrete;
    object.invoke();
}

use core::ops::Deref;

struct Value;

impl Value {
    fn inherent(&self) {}
}

trait Scale {
    fn scale(&self);
}

impl Scale for Value {
    fn scale(&self) {}
}

struct Wrapper(Value);

impl Deref for Wrapper {
    type Target = Value;

    fn deref(&self) -> &Value {
        loop {}
    }
}

fn main() {
    let value = Value;
    value.inherent();
    value.scale();
    Value::inherent(&value);
    <Value as Scale>::scale(&value);
    Wrapper(value).inherent();
}

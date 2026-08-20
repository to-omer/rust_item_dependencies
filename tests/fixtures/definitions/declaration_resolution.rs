const LIMIT: usize = 3;
const TAG: isize = 1;

trait Marker {}

struct DefaultType;

impl Marker for DefaultType {}

struct Container<T: Marker = DefaultType, const N: usize = LIMIT> {
    pub(crate) value: T,
}

enum Tag {
    First = TAG,
}

enum Choice {
    Second { value: u8 },
}

fn main() {
    let _: Container;
    let Choice::Second { value } = Choice::Second { value: 1 };
    let _ = value;
}

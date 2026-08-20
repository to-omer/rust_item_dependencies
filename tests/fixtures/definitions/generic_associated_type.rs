trait Bound {}

struct Concrete;

trait Family {
    type Item<'a>: Bound
    where
        Self: 'a;

    fn get<'a>(&'a self) -> Self::Item<'a>;
}

impl Bound for Concrete {}

impl Family for Concrete {
    type Item<'a> = Concrete;

    fn get<'a>(&'a self) -> Self::Item<'a> {
        Concrete
    }
}

fn capture<'a, T: Family>(value: T::Item<'a>) {
    let _ = || &value;
}

fn main() {}

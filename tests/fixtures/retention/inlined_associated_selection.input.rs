trait Transform {
    fn transform(value: u32) -> u32;
}

trait Storage {
    fn normalize(value: u32) -> u32 {
        value
    }
}

struct Value<M: Storage> {
    value: u32,
    marker: std::marker::PhantomData<M>,
}

impl<M: Storage> Value<M> {
    fn new(value: u32) -> Self {
        Self {
            value,
            marker: std::marker::PhantomData,
        }
    }

    #[inline(always)]
    fn get(self) -> u32 {
        M::normalize(self.value)
    }
}

impl<M: Transform> Storage for M {
    #[inline(always)]
    fn normalize(value: u32) -> u32 {
        M::transform(value)
    }
}

macro_rules! define_types {
    ($(($name:ident, $offset:expr, $alias:ident)),* $(,)?) => {
        $(
            enum $name {}

            impl Transform for $name {
                #[inline(always)]
                fn transform(value: u32) -> u32 {
                    value + $offset
                }
            }

            type $alias = Value<$name>;
        )*
    };
}

define_types!(
    (Unused, 40, UnusedValue),
    (Used, 6, UsedValue),
);

fn main() {
    let value = UsedValue::new(std::hint::black_box(1));
    assert_eq!(value.get(), 7);
}

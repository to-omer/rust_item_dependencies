macro_rules! direct_members {
    () => {
        trait Direct {
            fn kept(&self) -> u32;
fn dead(&self) -> u32;
        }

        struct DirectType;

        impl Direct for DirectType {
            fn kept(&self) -> u32 {
                7
            }

fn dead(&self) -> u32 {
                99
            }
        }
    };
}

direct_members!();

macro_rules! default_members {
    () => {
        trait Defaulted {
            fn required(&self) -> u32;

            fn fallback(&self) -> u32 {
                5
            }
        }

        struct Override;
        struct UsesDefault;

        impl Defaulted for Override {
            fn required(&self) -> u32 {
                11
            }

fn fallback(&self) -> u32 {
                99
            }
        }

        impl Defaulted for UsesDefault {
            fn required(&self) -> u32 {
                13
            }
        }
    };
}

default_members!();

macro_rules! repeated_members {
    ($( $name:ident => $value:expr),*) => {
        trait Repeated {
            $(fn $name(&self) -> u32;)*
        }

        struct RepeatedType;

        impl Repeated for RepeatedType {
            $(
                fn $name(&self) -> u32 {
                    $value
                }
            )*
        }
    };
}

repeated_members!(kept => 17, dead => 99);

fn require_direct<T: Direct>(value: &T) -> u32 {
    value.kept()
}

fn require_defaulted<T: Defaulted>(value: &T) -> u32 {
    value.required()
}

fn main() {
    assert_eq!(require_direct(&DirectType), 7);
    assert_eq!(require_defaulted(&Override), 11);
    assert_eq!(UsesDefault.fallback(), 5);
    assert_eq!(RepeatedType.kept(), 17);
}

macro_rules! choose_rule {
    ($one:ident; $discarded:ident) => {
        pub fn $one() -> u32 {
            99
        }

    };
    ($($many:ident),*) => {


        $(
            pub fn $many() -> u32 {
                7
            }
        )*
    };
}

mod selected_first {
    choose_rule!(kept; discarded);
}

mod selected_second {
    choose_rule!(kept, dead);
}

fn main() {
    assert_eq!(selected_first::kept(), 99);
    assert_eq!(selected_second::kept(), 7);
}

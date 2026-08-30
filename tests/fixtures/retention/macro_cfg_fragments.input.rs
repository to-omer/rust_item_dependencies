macro_rules! configured_fragments {
    ($discarded_item:ident,$live_function:ident,$discarded_field:ident,$discarded_parameter:ident,$discarded_statement_first:ident,$discarded_statement_last:ident) => {
#[cfg(any())]
pub fn $discarded_item() -> u8 {
            99
        }

        pub struct Record {
#[cfg_attr(all(), cfg(any()))]
pub $discarded_field: u8,
            pub kept: u8,
        }

        pub fn $live_function(
#[cfg(any())]
$discarded_parameter: u8,
            value: u8,
        ) -> u8 {
#[cfg(any())]
let $discarded_statement_first = 1;
#[cfg_attr(all(), cfg(any()))]
let $discarded_statement_last = 2;
            value
        }
    };
}

mod first {
    configured_fragments!(first_item,first_live,first_field,first_parameter,first_statement,first_statement_last);
}

mod second {
    configured_fragments!(second_item,second_live,second_field,second_parameter,second_statement,second_statement_last);
}

macro_rules! shared_cfg_fragment {
    ($condition:meta,$name:ident) => {
        pub struct Anchor;

        #[cfg($condition)]
        pub fn $name() -> u8 {
            5
        }
    };
}

mod shared_live {
    shared_cfg_fragment!(all(),kept);
}

mod shared_discarded {
    shared_cfg_fragment!(any(),discarded);
}

macro_rules! cfg_local_macro {
    ($discarded_macro:ident,$live_function:ident) => {
#[cfg(any())]
macro_rules! $discarded_macro {
    () => { 99 };
}

        pub fn $live_function() -> u8 {
            6
        }
    };
}

cfg_local_macro!(discarded_local_macro,local_live);

fn main() {
    let first = first::Record { kept: 3 };
    let second = second::Record { kept: 4 };
    let _ = shared_live::Anchor;
    let _ = shared_discarded::Anchor;
    assert_eq!(
        first::first_live(first.kept)
            + second::second_live(second.kept)
            + shared_live::kept(),
        12
    );
    assert_eq!(local_live(), 6);
}

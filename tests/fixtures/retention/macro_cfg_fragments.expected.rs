macro_rules! configured_fragments {
    ($live_function:ident,) => {


        pub struct Record {

            pub kept: u8,
        }

        pub fn $live_function(

            value: u8,
        ) -> u8 {


            value
        }
    };
}

mod first {
    configured_fragments!(first_live,);
}

mod second {
    configured_fragments!(second_live,);
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
    ($live_function:ident) => {


        pub fn $live_function() -> u8 {
            6
        }
    };
}

cfg_local_macro!(local_live);

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

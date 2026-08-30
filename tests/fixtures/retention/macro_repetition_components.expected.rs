macro_rules! star_items {
    ($( $name:ident => $value:expr => $ignored:expr),*) => {
        pub struct Anchor;
        $(
            pub fn $name() -> u32 {
                $value
            }
        )*
    };
}

mod star_many {
    star_items!(kept_a => 10 => "b", kept_b => 20 => "d");
}

mod star_only {
    star_items!();
}

macro_rules! plus_items {
    ($( $name:ident => $value:expr),+) => {
        pub struct Anchor;
        $(
            pub fn $name() -> u32 {
                $value
            }
        )+
    };
}

mod plus_many {
    plus_items!(kept_a => 30, kept_b => 40);
}

mod plus_only {
    plus_items!(only_dead => 4);
}

macro_rules! optional_item {
    ($(+ $name:ident)?) => {
        pub struct Anchor;
        $(
            pub fn $name() -> u32 {
                50
            }
        )?
    };
}

mod optional_kept {
    optional_item!(+ kept);
}

mod optional_dead {
    optional_item!();
}

macro_rules! leading_separator {
    ($(, $name:ident)*) => {
        pub struct Anchor;
        $(pub fn $name() -> u32 { 60 })*
    };
}

mod leading {
    leading_separator!(, kept);
}

macro_rules! trailing_separator {
    ($($name:ident,)*) => {
        pub struct Anchor;
        $(pub fn $name() -> u32 { 70 })*
    };
}

mod trailing {
    trailing_separator!(kept, );
}

macro_rules! no_separator {
    ($($name:ident)*) => {
        pub struct Anchor;
        $(pub fn $name() -> u32 { 80 })*
    };
}

mod adjacent {
    no_separator!(kept );
}

macro_rules! emit_lexical_item {
    (foo) => {
        pub fn left() -> u32 { 90 }
    };
    (+) => {

    };
    ("bar") => {
        pub fn right() -> u32 { 100 }
    };

}

macro_rules! lexical_items {
    ($($token:tt)*) => {
        $(emit_lexical_item!($token);)*
    };
}

mod lexical_boundary {
    lexical_items!(foo+"bar" );
}

macro_rules! expression_items {
    ($($name:ident),* => $value:expr) => {{

        $value
    }};
}

macro_rules! all_dead_repetition {
    ($( $name:ident),*) => {
        pub struct Anchor;

    };
}

mod all_dead {
    all_dead_repetition!();
}

fn main() {
    let _ = star_many::Anchor;
    let _ = star_only::Anchor;
    let _ = plus_many::Anchor;
    let _ = plus_only::Anchor;
    let _ = optional_kept::Anchor;
    let _ = optional_dead::Anchor;
    let _ = leading::Anchor;
    let _ = trailing::Anchor;
    let _ = adjacent::Anchor;
    let _ = all_dead::Anchor;
    let direct = expression_items!(=> 6);
    assert_eq!(
        star_many::kept_a()
            + star_many::kept_b()
            + plus_many::kept_a()
            + plus_many::kept_b()
            + optional_kept::kept()
            + leading::kept()
            + trailing::kept()
            + adjacent::kept()
            + lexical_boundary::left()
            + lexical_boundary::right(),
        550
    );
    assert_eq!(
        direct + expression_items!(nested_dead, nested_other => 7),
        13
    );
}

mod reduced_repetition {
    macro_rules! make {


        ($($unused:tt)*) => { pub fn value() -> u32 { 11 } };
    }


    make!();
}

mod reduced_capture {
    macro_rules! make {


        () => { pub fn value() -> u32 { 22 } };
    }

    #[allow(unused)]
    make!();
}

mod earlier_rule {
    macro_rules! make {
        () => { pub fn value() -> u32 { 99 } };
        ($($unused:tt)*) => { pub fn value() -> u32 { 7 } };
    }
    pub mod first { make!(); }
    pub mod second { make!(discarded); }

}

mod later_rule {
    macro_rules! make {
        ($discarded:ident; $name:ident) => { pub fn $name() -> u32 { 99 } };
        ($name:ident) => { pub fn $name() -> u32 { 7 } };
    }
    pub mod first { make!(discarded; value); }
    pub mod second { make!(value); }
}

fn main() {
    let values = [reduced_repetition::value(), reduced_capture::value(), earlier_rule::first::value(), earlier_rule::second::value(), later_rule::first::value(), later_rule::second::value()];
    assert_eq!(values, [11, 22, 99, 7, 99, 7]);
    println!("{}", values.iter().sum::<u32>());
}

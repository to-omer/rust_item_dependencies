mod origin {
    macro_rules! value {
        () => {
            1_u8
        };
    }
    macro_rules! unused {
        () => {
            2_u8
        };
    }

    pub(crate) use unused as unused_first;
    pub(crate) use value as first;
}

mod facade {
    pub(crate) use crate::origin::{first as second, unused_first as unused_second};
}

use crate::facade::{second as local_alias, unused_second as unused_alias};
use std::{println as print_alias, vec as unused_std_alias};

mod prefix_case {
    use crate::facade as facade_alias;

    pub fn run() {
        let _ = facade_alias::second!();
    }
}

fn main() {
    let _ = local_alias!();
    print_alias!("alias");
    println!("prelude");
    prefix_case::run();
}

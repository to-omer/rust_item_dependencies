#![allow(dead_code, unused_variables, unreachable_patterns)]

#[derive(Debug)]
struct Named {

    kept: i32,

    tail: i32,

}

struct Tuple(

    i32,

    i32,

);

union Number {

    kept: i32,
}

enum Choice {

    Unit,

    Tuple(

        i32,

    ),

    Struct {

        kept: i32,

    },
}

struct Record {
    kept: i32,
    carried: i32,
}

fn generic<

    'a,

    T,

    const N: usize,
>(

    value: &'a T,

    tail: i32,

) -> usize {
    std::mem::size_of_val(value) + N + tail as usize
}

struct Receiver(i32);

trait Scale {
    fn scale(&self,  value: i32) -> i32;
}

impl Scale for Receiver {
    fn scale(&self,  value: i32) -> i32 {
        self.0 * value
    }
}

impl Receiver {
    fn combine(
        &self,

        left: i32,

        right: i32,

    ) -> i32 {
        self.0 + left + right
    }
}

type Callback = fn( i32, ) -> i32;

fn identity( value: i32, ) -> i32 {
    value
}

fn combine(left: i32, right: i32) -> i32 {
    left + right
}

fn zero() -> i32 {
    0
}

fn disabled_tail() {

}

fn main() {
    let named = Named {

        kept: 1,

        tail: 4,

    };
    assert_eq!(format!("{named:?}"), "Named { kept: 1, tail: 4 }");
    let tuple = Tuple(

        5,

        8,

    );
    let number = Number { kept: 9 };

    let choices = [Choice::Unit, Choice::Tuple(10), Choice::Struct { kept: 11 }];
    let choice_sum: i32 = choices
        .into_iter()
        .map(|choice| match choice {

            Choice::Unit => 1,

            Choice::Tuple(value) => value,

            Choice::Struct {

                kept,

            } => kept,

        })
        .sum();

    let base = Record {
        kept: 12,
        carried: 13,
    };
    let updated = Record {

        ..base
    };
    let Record {

        carried,
        ..
    } = updated;

    let closure = |

        value: i32,

        tail: i32,

    | value + tail;
    let empty_closure = || 14;

    let array = [

        15,


        16,

    ];
    let empty_array: [i32; 0] = [];
    let tuple_expr = (

        17,


    );
    let unit = ();
    let tuple_suffix: (i32,) = (28, );
    let tuple_prefix: (i32,) = (

#[cfg(any())]
        panic!("tuple prefix required"),
        29
    );
    let called = combine(

        18,

        19,

    );
    let zero = zero();
    let method = Receiver(20).combine(

        21,

        22,

    );
    let scaled = Receiver(2).scale(3);
    let callback: Callback = identity;

    let matched = match 1 {

        1 => 30,

        _ => 32,
    };




    #[cfg(all())]
    let active_statement = 23;

    disabled_tail();
    let union_value = unsafe { number.kept };
    println!(
        "{}",
        named.kept
            + named.tail
            + tuple.0
            + tuple.1
            + union_value
            + choice_sum
            + carried
            + generic::<i32, 1>(&24, 25) as i32
            + closure(26, 27)
            + empty_closure()
            + array.into_iter().sum::<i32>()
            + empty_array.into_iter().sum::<i32>()
            + tuple_expr.0
            + std::mem::size_of_val(&unit) as i32
            + tuple_suffix.0
            + tuple_prefix.0
            + called
            + zero
            + method
            + scaled
            + callback(33)
            + matched
            + active_statement
    );
}

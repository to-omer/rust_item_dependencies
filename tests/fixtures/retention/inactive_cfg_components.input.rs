#![allow(dead_code, unused_variables, unreachable_patterns)]

#[derive(Debug)]
struct Named {
#[cfg(any())]
    gone_first: i32,
    kept: i32,
#[cfg_attr(all(), cfg(any()))]
    gone_middle: Vec<(i32, i32)>,
    tail: i32,
#[cfg(any())]
    gone_last: i32,
}

struct Tuple(
#[cfg(any())] i32,
    i32,
#[cfg(any())] Vec<(i32, i32)>,
    i32,
#[cfg(any())] i32,
);

union Number {
#[cfg(any())]
    gone: u64,
    kept: i32,
}

enum Choice {
#[cfg(any())]
    GoneUnit,
    Unit,
#[cfg(any())]
    GoneTuple(i32),
    Tuple(
#[cfg(any())] i32,
        i32,
#[cfg(any())] Vec<(i32, i32)>,
    ),
#[cfg(any())]
    GoneStruct { value: i32 },
    Struct {
#[cfg(any())]
        gone_first: i32,
        kept: i32,
#[cfg(any())]
        gone_last: i32,
    },
}

struct Record {
    kept: i32,
    carried: i32,
}

fn generic<
#[cfg(any())] 'gone,
    'a,
#[cfg(any())] Gone,
    T,
#[cfg(any())] const GONE: usize,
    const N: usize,
>(
#[cfg(any())] gone_first: i32,
    value: &'a T,
#[cfg(any())] gone_middle: Vec<(i32, i32)>,
    tail: i32,
#[cfg(any())] gone_last: i32,
) -> usize {
    std::mem::size_of_val(value) + N + tail as usize
}

struct Receiver(i32);

trait Scale {
    fn scale(&self, #[cfg(any())] gone: i32, value: i32) -> i32;
}

impl Scale for Receiver {
    fn scale(&self, #[cfg(any())] gone: i32, value: i32) -> i32 {
        self.0 * value
    }
}

impl Receiver {
    fn combine(
        &self,
#[cfg(any())] gone_first: i32,
        left: i32,
#[cfg_attr(all(), cfg(any()))] gone_middle: i32,
        right: i32,
#[cfg(any())] gone_last: i32,
    ) -> i32 {
        self.0 + left + right
    }
}

type Callback = fn(#[cfg(any())] i32, i32, #[cfg(any())] i32) -> i32;

fn identity(#[cfg(any())] gone_first: i32, value: i32, #[cfg(any())] gone_last: i32) -> i32 {
    value
}

fn combine(left: i32, right: i32) -> i32 {
    left + right
}

fn zero() -> i32 {
    0
}

fn disabled_tail() {
#[cfg(any())]
    panic!("disabled tail")
}

fn main() {
    let named = Named {
#[cfg(any())]
        gone_first: panic!("named first"),
        kept: 1,
#[cfg_attr(all(), cfg(any()))]
        gone_middle: vec![(2, 3)],
        tail: 4,
#[cfg(any())]
        gone_last: panic!("named last"),
    };
    assert_eq!(format!("{named:?}"), "Named { kept: 1, tail: 4 }");
    let tuple = Tuple(
#[cfg(any())]
        panic!("tuple first"),
        5,
#[cfg(any())]
        vec![(6, 7)],
        8,
#[cfg(any())]
        panic!("tuple last"),
    );
    let number = Number { kept: 9 };

    let choices = [Choice::Unit, Choice::Tuple(10), Choice::Struct { kept: 11 }];
    let choice_sum: i32 = choices
        .into_iter()
        .map(|choice| match choice {
#[cfg(any())]
            Choice::GoneUnit => 100,
            Choice::Unit => 1,
#[cfg(any())]
            Choice::GoneTuple(value) => value,
            Choice::Tuple(value) => value,
#[cfg(any())]
            Choice::GoneStruct { value } => value,
            Choice::Struct {
#[cfg(any())]
                gone_first,
                kept,
#[cfg(any())]
                gone_last,
            } => kept,
#[cfg(any())]
            _ => 200,
        })
        .sum();

    let base = Record {
        kept: 12,
        carried: 13,
    };
    let updated = Record {
#[cfg(any())]
        kept: panic!("update"),
        ..base
    };
    let Record {
#[cfg(any())]
        kept: gone,
        carried,
        ..
    } = updated;

    let closure = |
#[cfg(any())] gone_first: i32,
        value: i32,
#[cfg(any())] gone_middle: Vec<(i32, i32)>,
        tail: i32,
#[cfg(any())] gone_last: i32,
    | value + tail;
    let empty_closure = |#[cfg(any())] gone: i32| 14;

    let array = [
#[cfg(any())]
        panic!("array first"),
        15,
#[cfg(any())]
        panic!("array middle 1"),
#[cfg(any())]
        panic!("array middle 2"),
        16,
#[cfg(any())]
        panic!("array last"),
    ];
    let empty_array: [i32; 0] = [#[cfg(any())] panic!("only array")];
    let tuple_expr = (
#[cfg(any())]
        panic!("tuple expression first"),
        17,
#[cfg(any())]
        panic!("tuple expression suffix 1"),
#[cfg(any())]
        panic!("tuple expression suffix 2")
    );
    let unit = (#[cfg(any())] panic!("only tuple"),);
    let tuple_suffix: (i32,) = (28, #[cfg(any())] panic!("tuple suffix"));
    let tuple_prefix: (i32,) = (
#[cfg(any())]
        panic!("tuple prefix first"),
#[cfg(any())]
        panic!("tuple prefix required"),
        29
    );
    let called = combine(
#[cfg(any())]
        panic!("call first"),
        18,
#[cfg(any())]
        panic!("call middle"),
        19,
#[cfg(any())]
        panic!("call last"),
    );
    let zero = zero(#[cfg(any())] panic!("only call"));
    let method = Receiver(20).combine(
#[cfg(any())]
        panic!("method first"),
        21,
#[cfg(any())]
        panic!("method middle"),
        22,
#[cfg(any())]
        panic!("method last")
    );
    let scaled = Receiver(2).scale(3);
    let callback: Callback = identity;

    let matched = match 1 {
#[cfg(any())]
        0 => {}
        1 => 30,
#[cfg(any())]
        2 => 31,
        _ => 32,
    };

#[cfg(any())]
    let removed_let = panic!("let statement");
#[cfg(any())]
    panic!("expression statement");
#[cfg(any())]
    println!("macro statement");
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

trait Family {
    type Data;

    fn make(value: u8) -> Self::Data;
    fn take(data: Self::Data) -> u8;
}

struct Wrapper {
    value: u8,
}

struct Concrete;

impl Family for Concrete {
    type Data = Wrapper;

    fn make(value: u8) -> Self::Data {
        Self::Data { value }
    }

    fn take(data: Self::Data) -> u8 {
        let Self::Data { value } = data;
        value
    }
}

struct DeadWrapper {
    value: u8,
}

struct Dead;

impl Family for Dead {
    type Data = DeadWrapper;

    fn make(value: u8) -> Self::Data {
        Self::Data { value }
    }

    fn take(data: Self::Data) -> u8 {
        let Self::Data { value } = data;
        value
    }
}

fn unused() {}

fn main() {
    let data = <Concrete as Family>::make(7);
    println!("{}", <Concrete as Family>::take(data));
}

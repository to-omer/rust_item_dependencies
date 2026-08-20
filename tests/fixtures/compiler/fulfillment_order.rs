fn main() {
    let pairs = (0..3)
        .map(|left| (0..3).map(move |right| (left, right)))
        .flatten()
        .collect::<Vec<_>>();
    std::hint::black_box(pairs);
}

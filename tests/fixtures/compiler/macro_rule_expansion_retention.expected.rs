macro_rules! m {
(@dispatch $rule:ident) => {
    m!(@$rule);
};
(@keep) => {
    fn used() {}
};

(@named $name:ident) => {
    fn $name() {}
};
}

m!(@dispatch keep);


m!(@named shared_keep);


fn main() {
    used();
    shared_keep();
}

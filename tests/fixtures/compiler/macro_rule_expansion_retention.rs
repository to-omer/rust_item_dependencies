macro_rules! m {
(@dispatch $rule:ident) => {
    m!(@$rule);
};
(@keep) => {
    fn used() {}
};
(@dead) => {
    fn dead() {}
};
(@named $name:ident) => {
    fn $name() {}
};
}

m!(@dispatch keep);
m!(@dispatch dead);
m!(@named shared_dead_before);
m!(@named shared_keep);
m!(@named shared_dead_after);

fn main() {
    used();
    shared_keep();
}

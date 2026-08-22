extern crate external_wrapper;
extern crate external_leaf;

fn main() {
    let _ = external_wrapper::external_function();
    let _ = external_leaf::leaf_value();
}

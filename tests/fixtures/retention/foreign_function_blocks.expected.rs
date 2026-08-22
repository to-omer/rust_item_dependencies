

unsafe extern "C" {


#[link_name = "abs"]
fn renamed_abs(value: core::ffi::c_int) -> core::ffi::c_int;



}





fn main() {
    println!("{}", unsafe { renamed_abs(-7) });
}

type UnusedArgument = core::ffi::c_int;

unsafe extern "C" {
#[doc = "removed with the declaration"]
fn unused_before(value: UnusedArgument);

#[link_name = "abs"]
fn renamed_abs(value: core::ffi::c_int) -> core::ffi::c_int;

static UNUSED_STATIC: core::ffi::c_int;
fn unused_after();
}

unsafe extern "C" {
fn unused_block();
static UNUSED_BLOCK_STATIC: core::ffi::c_int;
}

fn unused_local() {}

fn main() {
    println!("{}", unsafe { renamed_abs(-7) });
}

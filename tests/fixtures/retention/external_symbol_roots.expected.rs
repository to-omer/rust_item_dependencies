fn function_dependency() -> i32 {
    1
}

#[unsafe(no_mangle)]
extern "C" fn exported_function() -> i32 {
    function_dependency()
}

const fn static_dependency() -> i32 {
    2
}

#[unsafe(export_name = "rid_exported_static")]
static EXPORTED_STATIC: i32 = static_dependency();

struct Receiver;

impl Receiver {
    #[unsafe(export_name = "rid_exported_method")]
    extern "C" fn method() -> i32 {
        3
    }
}

macro_rules! generate_export {
    () => {
        #[unsafe(export_name = "rid_generated_export")]
        extern "C" fn generated() -> i32 {
            4
        }
    };
}

generate_export!();



unsafe extern "C" {
    #[link_name = "exported_function"]
    fn imported_function() -> i32;
    #[link_name = "rid_exported_static"]
    static IMPORTED_STATIC: i32;
    #[link_name = "rid_exported_method"]
    fn imported_method() -> i32;
    #[link_name = "rid_generated_export"]
    fn imported_generated() -> i32;
}

fn main() {
    let result = unsafe {
        imported_function() + IMPORTED_STATIC + imported_method() + imported_generated()
    };
    println!("{result}");
}

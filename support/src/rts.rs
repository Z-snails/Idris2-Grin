use crate::string::GrinString;

#[no_mangle]
pub extern "C" fn _prim_crash(msg: &GrinString) -> ! {
    panic!("{}", msg);
}

#![allow(non_snake_case)]
use rug::Integer;

#[no_mangle]
unsafe extern "C" fn _prim_add_Integer(x: *mut Integer, y: *mut Integer) -> *mut Integer {
    Box::into_raw(Box::new(Integer::from(
        *Box::from_raw(x) + *Box::from_raw(y),
    )))
}

#[no_mangle]
unsafe extern "C" fn _prim_sub_Integer(x: *mut Integer, y: *mut Integer) -> *mut Integer {
    Box::into_raw(Box::new(Integer::from(
        *Box::from_raw(x) + *Box::from_raw(y),
    )))
}

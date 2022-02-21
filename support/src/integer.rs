#![allow(non_snake_case)]
use rug::Integer;

#[no_mangle]
pub extern "C" fn _prim_add_Integer(x: &Integer, y: &Integer) -> Box<Integer> {
    Box::new(Integer::from(x + y))
}

#[no_mangle]
pub extern "C" fn _prim_sub_Integer(x: &Integer, y: &Integer) -> Box<Integer> {
    Box::new(Integer::from(x - y))
}

#[no_mangle]
pub extern "C" fn _prim_clear_Integer(x: Box<Integer>) {
    drop(x);
}

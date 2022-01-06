use std::{
    alloc::{self, Layout},
    ptr::{copy_nonoverlapping, null},
};

#[repr(C)]
struct String {
    pub data: *const u8,
    pub length: u64,
}

unsafe extern "C" fn _prim_str_append(x: *const String, y: *const String) -> *const String {
    let x_len = (*x).length;
    let y_len = (*y).length;
    let length = x_len + y_len;
    let layout = match Layout::array::<u8>(length as usize) {
        Ok(layout) => layout,
        Err(_) => return null(),
    };
    let data = alloc::alloc(layout);
    copy_nonoverlapping((*x).data, data, x_len as usize);
    copy_nonoverlapping(
        (*y).data,
        (data as usize + x_len as usize) as *mut u8,
        y_len as usize,
    );
    Box::into_raw(Box::new(String { data, length }))
}

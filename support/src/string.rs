use std::{
    alloc::{alloc_zeroed, Layout},
    boxed::Box,
    fmt::{Display, self},
    ops::{Deref, DerefMut},
    ptr::NonNull,
    slice,
};

#[repr(C)]
pub struct GrinString {
    pub data: NonNull<u8>,
    pub length: u64,
}

impl GrinString {
    pub fn new_zeroed(length: u64) -> Self {
        let layout = Layout::array::<u8>(length as usize).expect("unvalid layout");
        let data =
            NonNull::new(unsafe { alloc_zeroed(layout) }).expect("alloc_zeroed returned null");
        GrinString { data, length }
    }
}

impl Deref for GrinString {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        unsafe { slice::from_raw_parts(self.data.as_ptr(), self.length as usize) }
    }
}

impl DerefMut for GrinString {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { slice::from_raw_parts_mut(self.data.as_ptr(), self.length as usize) }
    }
}

impl Display for GrinString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = std::str::from_utf8(unsafe {
            std::slice::from_raw_parts(self.data.as_ptr(), self.length as usize)
        })
        .map_err(|err| {
            eprintln!("utf-8 error: {}", err);
            fmt::Error
        })?;
        f.write_str(str)
    }
}

#[no_mangle]
pub extern "C" fn _prim_str_append(x: &GrinString, y: &GrinString) -> Box<GrinString> {
    let mut str = GrinString::new_zeroed(x.length + y.length);
    str[0..x.length as usize].copy_from_slice(x);
    str[x.length as usize..].copy_from_slice(y);
    Box::new(str)
}

mod tests {
    #[test]
    fn layout_correct() {
        use crate::string::GrinString;
        use std::mem::size_of;

        assert!(size_of::<GrinString>() == 16);
    }
}

use rug::Integer;
use crate::string::GrinString;

fn try_into_base_10(char: u8) -> Option<u8> {
    match char {
        b'0'..=b'9' => Some(char - b'0'),
        _ => None
    }
}

#[no_mangle]
pub extern "C" fn _prim_cast_String_Integer(string: &GrinString) -> Box<Integer> {
    let mut acc = Integer::ZERO;
    for &char in &string[..] {
        if let Some(digit) = try_into_base_10(char) {
            acc *= 10;
            acc += digit;
        } else {
            return Box::new(Integer::ZERO);
        }
    }
    Box::new(acc)
}

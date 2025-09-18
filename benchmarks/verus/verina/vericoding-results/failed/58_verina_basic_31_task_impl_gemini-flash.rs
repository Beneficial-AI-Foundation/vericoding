// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> bool
{
    'a' <= c && c <= 'z'
}

spec fn shift_minus_32(c: char) -> char
{
    arbitrary()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove duplicate shift_minus_32 and add CharUtils */
pub closed spec fn char_from_u8(u: u8) -> char {
    u as char
}

// A helper spec function to determine if a u8 represents a lowercase character.
pub closed spec fn is_lower_case_u8(u: u8) -> bool {
    'a' <= char_from_u8(u) && char_from_u8(u) <= 'z'
}

// A helper function to shift a u8 character by -32 (for uppercase conversion).
pub closed spec fn shift_minus_32_u8(u: u8) -> u8 {
    (u as int - 32) as u8
}
// </vc-helpers>

// <vc-spec>
fn to_uppercase(s: &str) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            let c = #[trigger] s@.index(i);
            let r = result@.index(i);
            if is_lower_case(c) {
                r == shift_minus_32(c)
            } else {
                r == c
            }
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix compilation errors regarding `array_index` method not found by using direct indexing and `as_slice().index()` for `Vec`. */
{
    let mut result_vec: Vec<u8> = Vec::new();
    let s_bytes = s.as_bytes();
    let s_len = s_bytes.len();

    let mut i: usize = 0;
    while i < s_len
        invariant
            0 <= i as int,
            i as int <= s_len as int,
            result_vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                let c_val_u8 = s_bytes.view()[j as usize];
                let r_val_u8 = result_vec.view().index(j);
                if is_lower_case_u8(c_val_u8) {
                    r_val_u8 == shift_minus_32_u8(c_val_u8)
                } else {
                    r_val_u8 == c_val_u8
                }
            },
        decreases s_len - i
    {
        let c_val = s_bytes[i];
        if is_lower_case_u8(c_val) {
            result_vec.push(shift_minus_32_u8(c_val));
        } else {
            result_vec.push(c_val);
        }
        i = i + 1;
    }
    let result_string = String::from_utf8_lossy(result_vec.as_slice()).to_string();
    result_string
}
// </vc-code>

}
fn main() {}
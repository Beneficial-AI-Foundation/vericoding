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
proof fn shift_minus_32_proof(c: char) -> (r: char)
    requires
        is_lower_case(c),
    ensures
        r == shift_minus_32(c),
{
    let c_code = c as u32;
    proof {
        assert('a' as u32 <= c_code && c_code <= 'z' as u32) by {
            assert(is_lower_case(c));
            assert('a' as u32 == 97 && 'z' as u32 == 122);
        }
        assert(c_code - 32 >= 0);
        assert(c_code >= 32);
    }
    let r_code = c_code - 32;
    let option_r = char::from_u32(r_code);
    assert(option_r.is_some()) by {
        assert(65 <= r_code && r_code <= 90);
    };
    let r_char = option_r.unwrap();
    r_char
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
{
    /* code modified by LLM (iteration 5): removed unsafe unwraps and used ASCII byte operations */
    let mut result_bytes: Vec<u8> = Vec::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i: usize = 0;
    
    while i < bytes.len()
        invariant
            result_bytes@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let c_byte = bytes[j];
                let r_byte = result_bytes@[j];
                if c_byte >= b'a' && c_byte <= b'z' {
                    r_byte == c_byte - 32
                } else {
                    r_byte == c_byte
                }
            },
        decreases bytes.len() - i,
    {
        let c_byte = bytes[i];
        let upper_byte = if c_byte >= b'a' && c_byte <= b'z' {
            c_byte - 32
        } else {
            c_byte
        };
        result_bytes.push(upper_byte);
        i += 1;
    }
    
    String::from_utf8(result_bytes).unwrap()
}
// </vc-code>

}
fn main() {}
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
    let mut result = String::new();
    let chars = s.chars();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let c = #[trigger] s@.index(j);
                let r = result@.index(j);
                if is_lower_case(c) {
                    r == shift_minus_32(c)
                } else {
                    r == c
                }
            },
    {
        let c = s.get_char(i);
        if c >= 'a' && c <= 'z' {
            let upper_c = ((c as u8) - 32) as char;
            result.push(upper_c);
        } else {
            result.push(c);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
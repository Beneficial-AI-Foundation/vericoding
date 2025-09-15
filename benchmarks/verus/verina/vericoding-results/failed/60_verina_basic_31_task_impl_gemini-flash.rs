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
spec fn shift_minus_32_real(c: char) -> char { ('A' as char).add( (c as char).sub('a' as char) as u32 ) }
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
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@.len() == i,
            // All characters processed so far satisfy the postcondition
            forall|j: int| 0 <= j < i ==> {
                let c = #[trigger] s@.index(j);
                let r = result@.index(j);
                if is_lower_case(c) {
                    r == shift_minus_32_real(c)
                } else {
                    r == c
                }
            },
    {
        let c = s.chars().nth(i as usize).unwrap();
        if is_lower_case(c) {
            result.push(shift_minus_32_real(c));
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
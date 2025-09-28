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
 /* helper modified by LLM (iteration 5): define executable function to convert lower to upper char, ensuring it matches the spec shift_minus_32 */

fn to_upper_char(c: char) -> (result : char)
    requires
        'a' <= c && c <= 'z',
    ensures
        result == shift_minus_32(c),
{
    ((c as u32) - 32) as char
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
/* code modified by LLM (iteration 5): implement string to uppercase conversion using loop and helper function */
{
    let mut result = String::new();
    for c in s.chars() {
        if is_lower_case(c) {
            let upper = to_upper_char(c);
            result.push(upper);
        } else {
            result.push(c);
        }
    }
    result
}
// </vc-code>

}
fn main() {}
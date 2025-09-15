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
/* helper modified by LLM (iteration 4): fix compilation error by using char::from_u32 */
exec fn exec_is_lower_case(c: char) -> bool {
    'a' <= c && c <= 'z'
}

exec fn exec_shift_minus_32(c: char) -> char {
    if exec_is_lower_case(c) {
        char::from_u32((c as u32) - 32).unwrap()
    } else {
        c
    }
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
    /* code modified by LLM (iteration 4): using fixed helpers */
    let mut result = String::new();
    for c in s.chars() {
        if exec_is_lower_case(c) {
            result.push(exec_shift_minus_32(c));
        } else {
            result.push(c);
        }
    }
    result
}
// </vc-code>

}
fn main() {}
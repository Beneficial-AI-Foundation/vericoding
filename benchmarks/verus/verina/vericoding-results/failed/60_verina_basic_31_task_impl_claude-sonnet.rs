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
/* helper modified by LLM (iteration 5): helper to safely convert str to char sequence */
spec fn str_to_char_at(s: &str, i: nat) -> char
    requires i < s@.len()
{
    s@.index(i as int)
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
    /* code modified by LLM (iteration 5): use String::new() and push() for proper string building */
    let mut result = String::new();
    let mut i: usize = 0;
    while i < s.unicode_len()
        invariant
            result@.len() == i,
            i <= s@.len(),
            forall|j: int| 0 <= j < i ==> {
                let c = s@.index(j);
                let r = result@.index(j);
                if is_lower_case(c) {
                    r == shift_minus_32(c)
                } else {
                    r == c
                }
            }
    {
        let c = str_to_char_at(s, i as nat);
        let new_char = if is_lower_case(c) {
            shift_minus_32(c)
        } else {
            c
        };
        result.push(new_char);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
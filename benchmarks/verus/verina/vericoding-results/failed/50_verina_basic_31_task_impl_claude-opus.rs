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
    /* code modified by LLM (iteration 5): Fixed push_char to push method for chars */
    let mut result = String::new();
    let mut i: usize = 0;
    while i < s.unicode_len()
        invariant
            0 <= i <= s@.len(),
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
        let new_c = if c >= 'a' && c <= 'z' {
            shift_minus_32(c)
        } else {
            c
        };
        result.push(new_c);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
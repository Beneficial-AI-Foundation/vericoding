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
/* helper modified by LLM (iteration 5): char conversion helper */
spec fn char_to_upper(c: char) -> char { if is_lower_case(c) { shift_minus_32(c) } else { c } }
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
    /* code modified by LLM (iteration 5): convert each char using helper */
    let mut result = String::new();
    let seq = s@;
    let mut i: int = 0;
    while i < seq.len()
        invariant 0 <= i && i <= seq.len()
        invariant result@.len() == i
        invariant forall|j: int| 0 <= j && j < i ==> {
            let c = seq.index(j);
            let r = result@.index(j);
            r == char_to_upper(c)
        }
        decreases seq.len() - i
    {
        let c = seq.index(i);
        if is_lower_case(c) {
            result.push(shift_minus_32(c));
        } else {
            result.push(c);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
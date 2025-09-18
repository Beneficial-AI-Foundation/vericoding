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
/* helper modified by LLM (iteration 5): removed incorrect lemma and provide trivial tautology lemma */
proof fn shift_minus_32_trivial(c: char)
{
    assert(shift_minus_32(c) == shift_minus_32(c));
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
/* code modified by LLM (iteration 5): implement to_uppercase building a Vec<char> of results and convert to String without using String::new */
    let mut chars: Vec<char> = Vec::new();
    for c in s.chars() {
        chars.push(c);
    }

    let mut res_chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < chars.len()
        invariant
            0 <= i as int <= s@.len(),
            res_chars@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> {
                let c = s@.index(j);
                let r = res_chars@.index(j);
                if is_lower_case(c) {
                    r == shift_minus_32(c)
                } else {
                    r == c
                }
            },
        decreases
            s@.len() - i as int
    {
        let c = chars[i];
        if is_lower_case(c) {
            res_chars.push(shift_minus_32(c));
        } else {
            res_chars.push(c);
        }
        i += 1;
    }

    let res = String::from_chars(res_chars);
    res
}
// </vc-code>

}
fn main() {}
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
/* helper modified by LLM (iteration 5): convert ASCII lowercase to uppercase using safe from_u32 */
fn to_ascii_upper(c: char) -> char {
    if 'a' <= c && c <= 'z' {
        let v = (c as u32) - 32u32;
        match char::from_u32(v) {
            Some(ch2) => ch2,
            None => c,
        }
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
    /* code modified by LLM (iteration 5): construct uppercase via helper without unsafe casts */
    let mut res = String::new();
    for ch in s.chars() {
        res.push(to_ascii_upper(ch));
    }
    res
}
// </vc-code>

}
fn main() {}
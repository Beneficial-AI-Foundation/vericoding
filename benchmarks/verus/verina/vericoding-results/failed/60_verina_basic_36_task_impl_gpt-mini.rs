// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): mapping spaces/commas/dots to colon */
spec fn map_space_comma_dot(c: char) -> char { if is_space_comma_dot(c) { ':' } else { c } }
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> 
            #[trigger] result@.index(i) == 
            if is_space_comma_dot(#[trigger] s@.index(i)) { ':' } else { s@.index(i) },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result by iterating characters and pushing mapped chars */
    let mut result = String::new();
    for c in s.chars() {
        if is_space_comma_dot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
    }
    result
}
// </vc-code>

}
fn main() {}
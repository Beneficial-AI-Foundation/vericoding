// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed helper function and relied on spec function only */
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
/* code modified by LLM (iteration 5): Fixed String initialization using Vec<char> conversion */
{
    let chars: Vec<char> = s.chars().collect();
    let mut result_vec = Vec::with_capacity(chars.len());
    for c in chars {
        if c == ' ' || c == ',' || c == '.' {
            result_vec.push(':');
        } else {
            result_vec.push(c);
        }
    }
    result_vec.into_iter().collect()
}
// </vc-code>

}
fn main() {}
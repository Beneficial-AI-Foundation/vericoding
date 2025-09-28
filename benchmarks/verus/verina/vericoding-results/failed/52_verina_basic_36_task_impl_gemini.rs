// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed. */
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
    /* code modified by LLM (iteration 5): switched to a for-loop over chars to fix compilation errors. */
    let mut result = String::new();
    proof {
        vstd::string::lemma_string_view_chars(s);
    }

    for c in s.chars()
        invariant
            result@.len() == i,
            forall|k: int| 0 <= k < i ==>
                #[trigger] result@.index(k) ==
                if is_space_comma_dot(#[trigger] s@.index(k)) { ':' } else { s@.index(k) },
    {
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
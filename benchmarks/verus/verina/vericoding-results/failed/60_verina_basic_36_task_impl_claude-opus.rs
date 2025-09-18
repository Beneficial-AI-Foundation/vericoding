// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Build string character by character using String methods */
    let mut result = String::new();
    let mut i = 0;
    while i < s.unicode_len()
        invariant
            0 <= i <= s@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result@.index(j) == 
                if is_space_comma_dot(#[trigger] s@.index(j)) { ':' } else { s@.index(j) },
    {
        let c = s.get_char(i);
        if c == ' ' || c == ',' || c == '.' {
            result.push_str(":");
        } else {
            result.push_char(c);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
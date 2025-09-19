// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
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
    // impl-start
    assume(false);
    "".to_string()
    // impl-end
}
// </vc-code>


}
fn main() {}
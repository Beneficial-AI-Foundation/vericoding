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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (v: String)
    ensures 
        v@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            if is_space_comma_dot(s@[i]) {
                v@[i] == ':'
            } else {
                v@[i] == s@[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
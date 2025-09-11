// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
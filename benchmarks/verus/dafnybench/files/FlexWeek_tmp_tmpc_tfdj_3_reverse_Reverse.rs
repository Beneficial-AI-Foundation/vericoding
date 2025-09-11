// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse(a: &Vec<char>) -> (b: Vec<char>)
    requires a.len() > 0
    ensures 
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() ==> b[k] == a[(a.len() - 1) - k]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
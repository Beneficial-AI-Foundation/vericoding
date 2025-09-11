// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn maxArray(a: &[int]) -> (m: int)
    requires a.len() >= 1,
    ensures 
        forall|k: int| 0 <= k < a.len() ==> m >= a@[k] &&
        exists|k: int| 0 <= k < a.len() && m == a@[k],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
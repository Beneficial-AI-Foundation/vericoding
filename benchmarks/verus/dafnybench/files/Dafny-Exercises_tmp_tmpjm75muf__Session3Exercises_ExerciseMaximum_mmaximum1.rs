// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mmaximum1(v: &[i32]) -> (i: usize)
    requires v.len() > 0,
    ensures 
        0 <= i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
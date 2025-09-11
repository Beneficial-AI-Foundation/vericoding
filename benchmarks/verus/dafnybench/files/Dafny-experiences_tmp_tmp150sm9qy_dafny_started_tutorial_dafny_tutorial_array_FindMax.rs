// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_max(a: &[i32]) -> (i: usize)

    requires 
        a.len() > 0,
    ensures
        i < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[i as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
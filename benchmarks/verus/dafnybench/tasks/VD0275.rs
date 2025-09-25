// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    sorted_a(a, a.len() as int)
}

spec fn sorted_a(a: &[int], i: int) -> bool {
    0 <= i <= a.len() && 
    forall|k: int| #![trigger a[k]] 0 < k < i ==> a[(k-1) as int] <= a[k]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn look_for_min(a: &[int], i: usize) -> (m: usize)
    requires 
        0 <= i < a.len(),
    ensures
        i <= m < a.len(),
        forall|k: int| #![trigger a[k]] i <= k < a.len() ==> a[k] >= a[m as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
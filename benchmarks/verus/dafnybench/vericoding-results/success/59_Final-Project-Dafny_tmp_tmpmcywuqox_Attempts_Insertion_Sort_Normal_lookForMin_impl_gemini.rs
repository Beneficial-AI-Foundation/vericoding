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
spec fn property_look_for_min(a: &[int], m: int, i: int, j: int) -> bool {
    forall|k: int| #![trigger a[k]] i <= k < j ==> a[k] >= a[m]
}
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
    let mut min_idx = i;
    let mut cur = i + 1;

    while cur < a.len()
        invariant
            0 <= i < a.len(),
            i <= min_idx < a.len(),
            i < cur <= a.len(),
            i <= min_idx < cur,
            property_look_for_min(a, min_idx as int, i as int, cur as int),
        decreases a.len() - cur
    {
        if a[cur] < a[min_idx] {
            min_idx = cur;
        }
        cur = cur + 1;
    }
    min_idx
}
// </vc-code>

}
fn main() {}
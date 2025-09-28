// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: Seq<int>) -> bool {
    forall|i: int| 1 <= i < a.len() ==> #[trigger] a[i] >= a[i-1]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_min(a: &[int], lo: usize) -> (minIdx: usize)
    requires 
        a.len() > 0,
        lo < a.len(),
    ensures 
        lo <= minIdx < a.len(),
        forall|x: int| lo <= x < a.len() ==> a[minIdx as int] <= a[x],
// </vc-spec>
// <vc-code>
{
    let mut min_idx = lo;
    let mut i = lo + 1;
    while i < a.len()
        invariant
            lo < i <= a.len(),
            lo <= min_idx < i,
            forall|k: int| lo <= k < i ==> a@[min_idx as int] <= a@[k],
        decreases a.len() - i
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
}
// </vc-code>

}
fn main() {}
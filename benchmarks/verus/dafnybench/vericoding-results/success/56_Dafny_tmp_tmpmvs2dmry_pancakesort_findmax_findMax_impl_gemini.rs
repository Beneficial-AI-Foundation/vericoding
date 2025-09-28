// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn findMax(a: &[i32], n: usize) -> (r: usize)
    requires
        a.len() > 0,
        0 < n <= a.len(),
    ensures
        0 <= r < n <= a.len(),
        forall|k: usize| 0 <= k < n <= a.len() ==> a[r as int] >= a[k as int],
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 1;
    let mut max_idx: usize = 0;
    while i < n
        invariant
            0 < n <= a.len(),
            1 <= i <= n,
            0 <= max_idx < i,
            forall|k: usize| (0 <= k < i) ==> a[max_idx as int] >= a[k as int],
        decreases n - i
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

}
fn main() {}
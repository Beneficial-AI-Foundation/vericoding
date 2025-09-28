// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_false_before_true(v: Seq<bool>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> !v[i] || v[j]
}

/* helper modified by LLM (iteration 5): removed helper that wasn't needed */
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    requires
        old(a).len() <= 100_000,
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed mutable borrow issue by reading value before first set */
    if a.len() == 0 {
        return;
    }
    
    let mut left: usize = 0;
    let mut right: usize = (a.len() - 1) as usize;
    
    while left < right
        invariant
            a.len() == old(a).len(),
            left <= a.len(),
            right < a.len(),
            left <= right + 1,
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|i: int| 0 <= i < left ==> !a[i],
            forall|i: int| right < i < a.len() ==> a[i],
            forall|i: int, j: int| 0 <= i < left && right < j < a.len() ==> !a[i] || a[j],
        decreases right - left
    {
        if !a[left] {
            left = left + 1;
        } else if a[right] {
            right = right - 1;
        } else {
            // Swap a[left] and a[right]
            let temp = a[left];
            let val_right = a[right];
            a.set(left, val_right);
            a.set(right, temp);
            
            left = left + 1;
            right = right - 1;
        }
    }
}
// </vc-code>

}
fn main() {}
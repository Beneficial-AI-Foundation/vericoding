// <vc-preamble>
use vstd::prelude::*;

verus! {

pub open spec fn is_sorted(a: &[i32], from: usize, to: usize) -> bool {
    &&& from <= to <= a.len()
    &&& forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_min(a: &mut [i32], from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= old(a).len(),
    ensures
        from <= index < to,
        forall|k: int| from <= k < to ==> old(a)[k] >= old(a)[index as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): carried function precondition into loop invariant */
    let mut min_index = from;
    let mut i = from + 1;
    while i < to
        invariant
            a.view() == old(a).view(),
            0 <= from < to <= old(a).len(),
            from < i <= to,
            from <= min_index < i,
            forall|k: int| from <= k < i ==> old(a)[k] >= old(a)[min_index as int],
        decreases to - i
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    min_index
}
// </vc-code>

}
fn main() {}
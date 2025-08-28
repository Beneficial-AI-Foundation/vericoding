use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_max(a: &[i32]) -> (i: usize)
    // Annotate this method with pre- and postconditions
    // that ensure it behaves as described.
    requires 
        a.len() > 0,
    ensures
        i < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[i as int],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn find_max(a: &[i32]) -> (i: usize)
    requires
        a.len() > 0,
    ensures
        i < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[i as int],
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;

    while i < a.len()
        invariant
            0 <= max_idx < a.len(),
            0 < i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] <= a[max_idx as int],
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

fn main() {}

}
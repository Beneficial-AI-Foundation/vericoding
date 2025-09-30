use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

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
// <vc-code>
{
    let mut max_idx = 0;
    let mut j = 1;
    
    while j < a.len()
        invariant
            0 <= max_idx < a.len(),
            1 <= j <= a.len(),
            forall|k: int| 0 <= k < j ==> a[k] <= a[max_idx as int],
        decreases a.len() - j,
    {
        if a[j] > a[max_idx] {
            max_idx = j;
        }
        j += 1;
    }
    
    max_idx
}
// </vc-code>

fn main() {}

}
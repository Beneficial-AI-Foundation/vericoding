use vstd::prelude::*;

verus! {

// <vc-helpers>
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
{
    let mut max_idx = 0;
    let mut i = 1;
    
    while i < a.len()
        invariant
            0 <= max_idx < a.len(),
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] <= a[max_idx as int],
        decreases a.len() - i,
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    max_idx
}
// </vc-code>

fn main() {}

}
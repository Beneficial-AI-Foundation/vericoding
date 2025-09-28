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
    let mut max_index = 0;
    for i in 1..a.len()
        invariant
            0 <= max_index < i,
            forall|k: int| 0 <= k < i ==> a[k] <= a[max_index as int]
    {
        if a[i] > a[max_index] {
            max_index = i;
        }
    }
    max_index
}
// </vc-code>

fn main() {}

}
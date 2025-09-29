use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn test_array_elements(a: &mut Vec<i32>, j: usize)
    requires 
        j < old(a).len(),
    ensures 
        a.len() == old(a).len(),
        a[j as int] == 60,
        forall|k: int| 0 <= k < a.len() && k != j ==> a[k] == old(a)[k],
// </vc-spec>
// <vc-code>
{
    a.set(j, 60);
}
// </vc-code>

fn main() {}

}
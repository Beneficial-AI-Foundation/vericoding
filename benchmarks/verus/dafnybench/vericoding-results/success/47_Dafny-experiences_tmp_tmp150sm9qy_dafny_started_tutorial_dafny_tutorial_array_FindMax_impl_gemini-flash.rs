use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[allow(unused_mut)]
pub fn abs_diff(x: i32, y: i32) -> u32 {
    (x - y).abs() as u32
}
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
    let mut max_idx: usize = 0;
    let mut i: usize = 1;

    while i < a.len()
        invariant
            i <= a.len(),
            max_idx < i,
            forall|k: int| 0 <= k < i ==> a[k] <= a[max_idx as int],
        decreases a.len() - i,
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
use vstd::prelude::*;

verus! {

//Algorithm 1: From left to right return the first

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mmaximum1(v: &[i32]) -> (i: usize)
    requires v.len() > 0,
    ensures 
        0 <= i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k],
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut max_idx: usize = 0;

    if v.len() == 0 {
        // This case should ideally be prevented by the pre-condition `v.len() > 0`.
        // If it were to happen, returning 0 might be an arbitrary but safe default,
        // although it violates the post-condition `0 <= i < v.len()`.
        // Given the pre-condition, this block is unreachable at runtime.
        // We include it to satisfy the type system if `v.len()` could be 0,
        // which it cannot under the current `requires` clause.
        return 0;
    }

    // Initialize max_idx and i to handle the first element
    // The loop invariant needs max_idx to be valid for at least one element.
    // If v.len() > 0, v[0] is a valid initial maximum.
    max_idx = 0;
    i = 1;

    while i < v.len()
        invariant
            0 < i && i <= v.len(), // i starts at 1, so 0 < i
            0 <= max_idx && max_idx < i,
            forall|k: int| 0 <= k < i ==> v[max_idx as int] >= v[k],
        decreases v.len() - i
    {
        if v[i] > v[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left

fn main() {
}

}
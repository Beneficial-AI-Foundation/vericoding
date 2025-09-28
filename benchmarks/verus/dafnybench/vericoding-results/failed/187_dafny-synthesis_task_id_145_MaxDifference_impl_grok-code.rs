use vstd::prelude::*;

verus! {

// <vc-helpers>
// (empty - no updates needed)
// </vc-helpers>

// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut min_val = a[0];
    for idx in 1..a.len() {
        invariant(
            0 <= idx <= a.len(),
            forall |k: int| 0 <= k < idx ==> max_val >= a@[k] && min_val <= a@[k]
        );
        if a[idx] > max_val {
            max_val = a[idx];
        }
        if a[idx] < min_val {
            min_val = a[idx];
        }
    }
    proof {
        assert forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() implies a@[i] - a@[j] <= max_val - min_val by {
            assert(a@[i] <= max_val);
            assert(min_val <= a@[j]);
        }
    }
    max_val - min_val
}
// </vc-code>

fn main() {
}

}
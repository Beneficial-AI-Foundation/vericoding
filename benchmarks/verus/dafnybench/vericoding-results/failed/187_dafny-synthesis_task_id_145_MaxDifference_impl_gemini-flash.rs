use vstd::prelude::*;

verus! {

// <vc-helpers>
fn max_val_in_range(a: &[i32], start: int, end: int) -> (max_v: i32)
    requires
        0 <= start <= a.len(),
        0 <= end <= a.len(),
        start < end, // Range must be non-empty
    ensures
        forall|i: int| start <= i < end ==> a[i] <= max_v,
        exists|i: int| start <= i < end && a[i] == max_v,
{
    let mut current_max = a[start as usize];
    let mut i: int = start + 1;

    #[verifier::loop_invariant(
        start <= i && i <= end, // Corrected range for `i`
        forall|k: int| start <= k < i ==> a[k] <= current_max,
        exists|k: int| start <= k < i && a[k] == current_max,
    )]
    while i < end
    {
        if a[i as usize] > current_max {
            current_max = a[i as usize];
        }
        i = i + 1;
    }
    current_max
}

fn min_val_in_range(a: &[i32], start: int, end: int) -> (min_v: i32)
    requires
        0 <= start <= a.len(),
        0 <= end <= a.len(),
        start < end, // Range must be non-empty
    ensures
        forall|i: int| start <= i < end ==> a[i] >= min_v,
        exists|i: int| start <= i < end && a[i] == min_v,
{
    let mut current_min = a[start as usize];
    let mut i: int = start + 1;

    #[verifier::loop_invariant(
        start <= i && i <= end, // Corrected range for `i`
        forall|k: int| start <= k < i ==> a[k] >= current_min,
        exists|k: int| start <= k < i && a[k] == current_min,
    )]
    while i < end
    {
        if a[i as usize] < current_min {
            current_min = a[i as usize];
        }
        i = i + 1;
    }
    current_min
}
// </vc-helpers>

// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
    let n = a.len() as int;
    assert(n > 1);

    // The maximum difference between any two elements in the array can simply be found by
    // taking the maximum element and subtracting the minimum element.
    // Let max_v = max(a[0], ..., a[n-1]) and min_v = min(a[0], ..., a[n-1]).
    // For any i, j, we have a[i] <= max_v and a[j] >= min_v.
    // Thus, a[i] - a[j] <= max_v - min_v.
    // The equality can be achieved by picking the index of max_v for i and index of min_v for j.

    let max_a = max_val_in_range(a, 0, n);
    let min_a = min_val_in_range(a, 0, n);

    let final_diff = max_a - min_a;

    // Proof to satisfy the postcondition.
    // We need to show that forall i, j, a[i] - a[j] <= final_diff.
    // This is true because max_a >= a[i] for all i, and min_a <= a[j] for all j.
    // Therefore, a[i] - a[j] <= max_a - min_a.
    proof {
        assert forall|idx_i: int, idx_j: int| 0 <= idx_i < n && 0 <= idx_j < n
        implies a[idx_i] - a[idx_j] <= final_diff by {
            // from max_val_in_range postcondition, a[idx_i] <= max_a
            assert(a[idx_i] <= max_a);
            // from min_val_in_range postcondition, a[idx_j] >= min_a
            assert(a[idx_j] >= min_a);
            assert(a[idx_i] - a[idx_j] <= max_a - min_a);
        };
    }

    final_diff
}
// </vc-code>

fn main() {
}

}
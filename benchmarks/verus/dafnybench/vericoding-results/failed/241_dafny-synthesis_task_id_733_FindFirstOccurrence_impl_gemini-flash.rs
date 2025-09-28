use vstd::prelude::*;

verus! {

// <vc-helpers>
fn check_first_occurrence_proof(arr: &[i32], target: i32, result: int, i: int)
    requires
        0 <= result < arr.len(),
        arr[result as usize] == target,
        forall|k: int| 0 <= k < result ==> arr[k as usize] < target,
        forall|idx: int, jdx: int| 0 <= idx < jdx < arr.len() ==> arr[idx as usize] <= arr[jdx as usize],
        0 <= i < result,
    ensures
        arr[i as usize] != target,
        arr[i as usize] < target,
{
    // Need to prove arr[i] < target
    // We know that forall|k: int| 0 <= k < result ==> arr[k] < target
    // And we have 0 <= i < result, so arr[i] < target follows directly from the assumption.
}

fn check_no_occurrence_proof(arr: &[i32], target: i32, len: int)
    requires
        forall|k: int| 0 <= k < len ==> arr[k as usize] < target,
        len == arr.len() as int,
        forall|idx: int, jdx: int| 0 <= idx < jdx < arr.len() ==> arr[idx as usize] <= arr[jdx as usize],
    ensures
        forall|k: int| 0 <= k < arr.len() ==> arr[k as usize] != target,
{
    // If arr[k] < target for all k, then arr[k] != target for all k.
    // This is direct from inequality.
}

fn check_no_occurrence_proof_upper_bound(arr: &[i32], target: i32, low: int, high: int)
    requires
        forall|k: int| low <= k < high ==> arr[k as usize] != target,
        low == 0,
        high == arr.len() as int,
    ensures
        forall|k: int| 0 <= k < arr.len() ==> arr[k as usize] != target,
{
    // Direct consequence
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &[i32], target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures
        (0 <= result < arr.len() ==> arr[result as int] == target) &&
        (result == -1 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] != target)
// </vc-spec>
// <vc-code>
{
    let mut low: i32 = 0;
    let mut high: i32 = arr.len() as i32;
    let mut result: i32 = -1;

    let mut low_idx: int = 0;
    let mut high_idx: int = arr.len() as int; // Exclusive upper bound

    // Invariant:
    // 1. 0 <= low_idx <= high_idx <= arr.len()
    // 2. forall k: int, 0 <= k < low_idx ==> arr[k as usize] < target
    // 3. forall k: int, high_idx <= k < arr.len() ==> arr[k as usize] >= target
    // This invariant is strong enough to find the first element >= target.
    // If arr[low_idx] == target at the end, it must be the first.

    while low_idx < high_idx
        invariant
            0 <= low_idx <= high_idx <= arr.len(),
            forall|k_inv: int| 0 <= k_inv < low_idx ==> arr[k_inv as usize] < target, #[trigger] arr[k_inv as usize],
            forall|k_inv: int| high_idx <= k_inv < arr.len() ==> arr[k_inv as usize] >= target, #[trigger] arr[k_inv as usize],
            arr.len() as int == high as int, // Ghost value for arr.len()
            low_idx == low as int,
            high_idx == high as int
    {
        let mid_idx: int = low_idx + (high_idx - low_idx) / 2;
        assert(low_idx <= mid_idx && mid_idx < high_idx); // mid_idx is always valid and within bounds

        if arr[mid_idx as usize] < target {
            // arr[mid_idx] is definitely not the target, and any element before it will also be < target
            // (due to sorted property and mid_idx being less than actual target position if it exists).
            // So, we can safely advance low_idx to mid_idx + 1.
            low_idx = mid_idx + 1;
            low = low_idx as i32;
        } else { // arr[mid_idx] >= target
            // This mid_idx *could* be the first occurrence of target, or an element > target.
            // It definitely means that any first occurrence of target must be at or before mid_idx.
            // So we try setting high_idx to mid_idx.
            high_idx = mid_idx;
            high = high_idx as i32;
        }
    }

    // After the loop, low_idx == high_idx.
    // The invariant implies:
    // 1. forall k: int, 0 <= k < low_idx ==> arr[k] < target
    // 2. forall k: int, low_idx <= k < arr.len() ==> arr[k] >= target

    // At this point, low_idx is the index of the first element that is >= target.
    // We need to check if arr[low_idx] is actually equal to target.
    if low_idx < arr.len() as int && arr[low_idx as usize] == target {
        // We found it, and low_idx is the first such element.
        // We need to prove:
        // 1. arr[low_idx] == target (checked by if condition)
        // 2. Forall k < low_idx, arr[k] != target (implied by invariant 1: arr[k] < target)
        // We also need to prove that if result != -1, then 0 <= result < arr.len() which is satisfied by low_idx < arr.len().

        proof {
            // Prove forall k: int, 0 <= k < low_idx ==> arr[k] != target
            // From invariant, we know forall k: int, 0 <= k < low_idx ==> arr[k] < target
            // If arr[k] < target, then arr[k] != target. This is trivial.
            assert forall |k_assert: int| 0 <= k_assert < low_idx implies arr[k_assert as usize] != target by {
                assert(arr[k_assert as usize] < target); // From invariant
            }
        }
        low_idx as i32
    } else {
        // If low_idx == arr.len(), it means all elements are < target.
        // If arr[low_idx] != target (and low_idx < arr.len()), it means arr[low_idx] > target,
        // and since it's sorted, all subsequent elements are also > target.
        // So target is not in the array.
        proof {
            if low_idx == arr.len() as int {
                // Case 1: low_idx reached arr.len()
                // All elements 0 to arr.len()-1 are < target
                assert forall |k_assert: int| 0 <= k_assert < arr.len() implies arr[k_assert as usize] < target by {
                    assert(0 <= k_assert && (k_assert as int) < low_idx); // Because low_idx == arr.len()
                    assert(arr[k_assert as usize] < target); // By invariant
                }
                check_no_occurrence_proof(arr, target, arr.len() as int);
            } else {
                // Case 2: low_idx < arr.len() but arr[low_idx] != target (meaning arr[low_idx] > target given the invariant)
                // We need to prove forall|i: int| 0 <= i < arr.len() ==> arr[i] != target
                assert(arr[low_idx as usize] >= target); // From invariant
                assert(arr[low_idx as usize] != target); // From condition
                assert(arr[low_idx as usize] > target); // Therefore
                assert forall |k_assert: int| 0 <= k_assert < arr.len() implies arr[k_assert as usize] != target by {
                    if k_assert < low_idx {
                        assert(arr[k_assert as usize] < target); // By invariant
                    } else { // k >= low_idx
                        assert(arr[k_assert as usize] >= arr[low_idx as usize]); // By sorted property
                        assert(arr[k_assert as usize] > target); // Transitivity
                    }
                }
            }
        }
        -1
    }
}
// </vc-code>

fn main() {
}

}
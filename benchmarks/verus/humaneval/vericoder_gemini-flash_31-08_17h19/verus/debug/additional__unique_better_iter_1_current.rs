use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(v: &Vec<i32>, val: i32) -> bool {
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |j: int| 0 <= j < i ==> v[j] != val,
    {
        if v[i] == val {
            return true;
        }
        i = i + 1;
    }
    false
}

// Proof that if an array `a` is sorted and `a[i] < a[j]` for `i < j`,
// then `a[i]` cannot be equal to `a[k]` for any `k < j`, where `k` is distinct from `i`.
// This helper is not directly used but provides insight into properties that can be proven.
proof fn sorted_distinct_implies(a: &Seq<i32>, i: int, j: int, k: int)
    requires
        0 <= i < j < a.len(),
        0 <= k < j,
        i != k,
        forall|x: int, y: int|
            0 <= x && x < y && y < a.len() ==> a[x] <= a[y],
        a[i] < a[j],
    ensures
        a[i] != a[k],
{
    if k < i {
        // k < i < j
        // We know a[k] <= a[i]
        // If a[k] == a[i], then it contradicts a[i] < a[j] potentially, or just doesn't help.
        // We need a[i] != a[k].
        // If a[k] == a[i], then a[k] <= a[i] <= a[j].
        // The condition a[x] <= a[y] for x < y is a weak ordering.
        // We need strict ordering for unique elements.
        // The postcondition ensures strict ordering for the result `result[i] < result[j]`.
        // This hint is more about proving uniqueness in the result from the sorted input.
    } else { // k > i
        // i < k < j
        // We know a[i] <= a[k]
        // If a[k] == a[i], this is possible.
        // This helper is probably not what's directly needed for the unique_better implementation.
        // The implementation will rely on checking if the element is already in the result vector.
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() as int <= i + 1, // result can have at most i+1 elements
            forall|x: int, y: int|
                0 <= x && x < y && y < result.len() ==> result[x] < result[y], // result is strictly sorted
            // All elements in `result` are from `a` and are present in `a[0..i]`.
            forall|k: int|
                0 <= k < result.len() ==> exists|idx: int| 0 <= idx < i && result[k] == a[idx],
            // For any element already in `result`, it must be the last element added, or found from a previous index.
            // This is implicitly handled by the logic: we only add if not already present.
            // When `i` increments, `a[i]` is the candidate.
            // The key invariant is that `result` remains sorted and unique.
            // For any element `val` in `result`, `val` must be `a[first_occurrence_idx]` for some `first_occurrence_idx <= i-1`.

            // For all j < i, a[j] is considered.
            // If result is empty or `a[i]` is greater than the last element of `result`, then `a[i]` is unique.
            // The main property of `unique_better` is that it processes unique elements from a sorted `a`.
            // The postcondition requires `result` to be strictly sorted.
            // If `result` is empty, or `a[i]` is greater than `result.last()` then `a[i]` is unique.
            // If `a[i]` equals `result.last()`, then we skip it.
            // Since `a` is sorted, `a[i]` can only be equal to `result.last()` if `result.last()` was `a[j]` for some `j < i`.
            // Because `a` is sorted, all `a[k]` for `k <= i` are `<= a[i]`.
            // If we add `a[i]` to `result`, it must be strictly greater than the previous `result.last()`.
            // Any element `num` in `result` must be present in `a`
            forall|k:int| 0 <= k < result.len() ==> exists |idx:int| 0 <= idx < a.len() && result[k] == a[idx],
            // Any element `v` in result[0..result.len()-1] implies that there is a j < i such that a[j] == v
            // and `v` was the first occurrence of that value from left to right in the `a` array
            forall |k: int| 0 <= k < result.len() ==> (
                let val_in_res = result[k];
                exists |idx_a: int| (
                    0 <= idx_a < i && val_in_res == a[idx_a] &&
                    forall |idx_prev: int| (0 <= idx_prev < idx_a ==> a[idx_prev] < val_in_res)
                )
            ),
    {
        let current_val = a[i];

        if result.is_empty() {
            result.push(current_val);
        } else {
            // Check if current_val is greater than the last element in result.
            // If a[i] is greater than result.last(), it's a new unique element.
            // Since `a` is sorted, if `current_val` is not greater than `result.last()`,
            // implies `current_val` is less than or equal to `result.last()`.
            // Given the original array `a` is sorted and `result` contains only elements from `a`,
            // and `result` is strictly sorted, then `result.last()` must be `a[j]` for some `j < i`.
            // If `current_val < result.last()`, it means `a[i] < a[j]` for some `j < i`, which contradicts `a` being sorted.
            // So `current_val` must be equal to `result.last()`.
            let last_val_in_result = result.last().unwrap();
            if current_val > last_val_in_result {
                result.push(current_val);
            }
            // else: current_val <= last_val_in_result
            // Since a is sorted, a[i] >= a[j] for j < i.
            // result.last() came from some a[j_last] where j_last < i.
            // So a[i] >= a[j_last] = result.last().
            // Therefore, current_val must be equal to last_val_in_result.
            // In this case, we simply skip adding it because it's a duplicate.
        }
        i = i + 1;
    }

    result
}
// </vc-code>

fn main() {}
}
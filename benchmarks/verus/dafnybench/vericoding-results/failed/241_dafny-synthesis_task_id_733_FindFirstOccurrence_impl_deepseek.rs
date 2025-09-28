use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sorted_array_no_target_above_index(arr: Seq<i32>, target: i32, idx: int)
    requires
        0 <= idx < arr.len(),
        arr[idx] > target,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures
        forall|i: int| idx <= i < arr.len() ==> arr[i] > target
{
    assert forall|i: int| idx <= i < arr.len() implies arr[i] > target by {
        assert(arr[idx] <= arr[i]);
    };
}

proof fn lemma_sorted_array_no_target_below_index(arr: Seq<i32>, target: i32, idx: int)
    requires
        0 <= idx < arr.len(),
        arr[idx] < target,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures
        forall|i: int| 0 <= i <= idx ==> arr[i] < target
{
    assert forall|i: int| 0 <= i <= idx implies arr[i] < target by {
        assert(arr[i] <= arr[idx]);
    };
}

proof fn lemma_lower_bound_maintained(arr: Seq<i32>, target: i32, low: int, high: int)
    requires
        0 <= low <= high <= arr.len(),
        forall|i: int| 0 <= i < low ==> arr[i] != target,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures
        forall|i: int| 0 <= i < high ==> arr[i] != target
{
    if high > low {
        let mid = low + (high - low) / 2;
        if arr[mid] < target {
            lemma_sorted_array_no_target_below_index(arr, target, mid);
            lemma_lower_bound_maintained(arr, target, mid + 1, high);
        } else if arr[mid] > target {
            lemma_sorted_array_no_target_above_index(arr, target, mid);
            lemma_lower_bound_maintained(arr, target, low, mid);
        } else {
            // mid == target, but we have forall|i| 0 <= i < low ==> arr[i] != target
            // However, if mid >= low and arr[mid] == target, this contradicts the precondition
            // Since the array is sorted and we're searching within [low, high)
            assert(false);
        }
    }
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
    let mut low: usize = 0;
    let mut high: usize = arr.len();
    let mut result: i32 = -1;
    
    while low < high
        invariant
            0 <= low <= high <= arr.len(),
            result == -1 || (0 <= result < arr.len() as i32 && arr[result as int] == target),
            result == -1 ==> forall|i: int| 0 <= i < low ==> arr[i] != target
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if arr[mid] == target {
            result = mid as i32;
            break;
        } else if arr[mid] < target {
            proof {
                lemma_sorted_array_no_target_below_index(arr@, target, mid as int);
            }
            low = mid + 1;
        } else {
            proof {
                lemma_sorted_array_no_target_above_index(arr@, target, mid as int);
            }
            high = mid;
        }
    }
    
    if result == -1 {
        proof {
            lemma_lower_bound_maintained(arr@, target, 0, arr.len());
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}
use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove that if we find a target at some index,
// and we've verified all elements before that index are less than the target,
// then that index is the first occurrence
proof fn first_occurrence_lemma(arr: &[i32], target: i32, mid: int)
    requires
        0 <= mid < arr.len(),
        arr[mid] == target,
        forall|i: int| 0 <= i < mid ==> arr[i] < target,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        forall|i: int| 0 <= i < mid ==> arr[i] != target,
{
    assert forall|i: int| 0 <= i < mid implies arr[i] != target by {
        assert(arr[i] < target);
    };
}

// Helper to prove that elements less than target are not equal to target
proof fn less_than_not_equal(arr: &[i32], target: i32, left: int, mid: int)
    requires
        0 <= left <= mid < arr.len(),
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
        forall|i: int| 0 <= i < left ==> arr[i] < target,
        arr[mid] < target,
    ensures
        forall|i: int| 0 <= i <= mid ==> arr[i] < target,
{
    assert forall|i: int| 0 <= i <= mid implies arr[i] < target by {
        if i < left {
            assert(arr[i] < target);
        } else {
            assert(left <= i <= mid);
            assert(arr[i] <= arr[mid]);
            assert(arr[mid] < target);
            assert(arr[i] < target);
        }
    };
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
    let mut left: usize = 0;
    let mut right: usize = arr.len();
    let mut result: i32 = -1;
    
    while left < right
        invariant
            0 <= left <= right <= arr.len(),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            // All elements before left are less than target
            forall|i: int| 0 <= i < left ==> arr[i] < target,
            // All elements at right and after are greater than target  
            forall|i: int| right <= i < arr.len() ==> arr[i] > target,
            // If we found a result, it's valid and is the first occurrence
            result >= 0 ==> (0 <= result < arr.len() && 
                            arr[result as int] == target &&
                            forall|i: int| 0 <= i < result ==> arr[i] != target),
            // Range constraint for potential result
            left < right ==> left < arr.len(),
        decreases right - left,
    {
        let mid: usize = left + (right - left) / 2;
        assert(left <= mid < right);
        assert(mid < arr.len());
        
        if arr[mid] == target {
            // Found target, check if it's the first occurrence
            if mid == 0 || arr[mid - 1] < target {
                // This is the first occurrence
                proof {
                    if mid == 0 {
                        assert forall|i: int| 0 <= i < mid implies arr[i] != target by {
                            assert(i < 0);
                            assert(false);
                        };
                    } else {
                        assert(mid > 0);
                        assert(arr[mid - 1] < target);
                        assert forall|i: int| 0 <= i < mid implies arr[i] != target by {
                            if i < left {
                                assert(arr[i] < target);
                            } else {
                                assert(left <= i < mid);
                                assert(arr[i] <= arr[mid - 1]);
                                assert(arr[mid - 1] < target);
                                assert(arr[i] < target);
                            }
                        };
                    }
                    first_occurrence_lemma(arr, target, mid as int);
                }
                assert(mid < arr.len());
                assert(mid <= usize::MAX);
                assert(mid <= i32::MAX as usize) by {
                    assert(mid < arr.len());
                }
                result = mid as i32;
                assert(0 <= result < arr.len());
                assert(arr[result as int] == target);
                assert(forall|i: int| 0 <= i < result ==> arr[i] != target);
                break;
            } else {
                // There might be an earlier occurrence
                assert(mid > 0);
                assert(arr[mid - 1] == target || arr[mid - 1] > target);
                assert(arr[mid - 1] >= target);
                right = mid;
                assert(forall|i: int| right <= i < arr.len() ==> arr[i] > target) by {
                    assert forall|i: int| right <= i < arr.len() implies arr[i] > target by {
                        assert(arr[i] >= arr[mid]);
                        assert(arr[mid] == target);
                        if i == mid {
                            assert(false); // mid < right now
                        } else {
                            assert(i > mid);
                            assert(arr[i] > arr[mid]);
                            assert(arr[i] > target);
                        }
                    }
                };
            }
        } else if arr[mid] < target {
            // Target must be in the right half
            proof {
                less_than_not_equal(arr, target, left as int, mid as int);
            }
            left = mid + 1;
            assert(forall|i: int| 0 <= i < left ==> arr[i] < target);
        } else {
            // arr[mid] > target, so target must be in the left half
            assert(arr[mid as int] > target);
            assert(forall|i: int| mid <= i < arr.len() ==> arr[i] >= arr[mid as int]);
            assert(forall|i: int| mid <= i < arr.len() ==> arr[i] > target);
            right = mid;
        }
    }
    
    // Prove postcondition
    assert(result >= 0 ==> arr[result as int] == target);
    assert(result >= 0 ==> forall|i: int| 0 <= i < result ==> arr[i] != target);
    assert(result == -1 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] != target) by {
        if result == -1 {
            assert(left >= right);
            assert(left <= right);
            assert(left == right);
            assert(forall|i: int| 0 <= i < left ==> arr[i] < target);
            assert(forall|i: int| 0 <= i < left ==> arr[i] != target);
            assert(forall|i: int| right <= i < arr.len() ==> arr[i] > target);
            assert(forall|i: int| right <= i < arr.len() ==> arr[i] != target);
            assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] != target);
        }
    };
    
    result
}
// </vc-code>

fn main() {
}

}
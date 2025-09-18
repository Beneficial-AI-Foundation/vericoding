// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed trigger annotations in proof */
spec fn binary_search_index(arr: &Vec<i32>, target: i32, low: int, high: int) -> int
    decreases high - low
{
    if low >= high {
        -1
    } else {
        let mid = low + (high - low) / 2;
        if arr[mid] == target {
            if mid == 0 || arr[mid - 1] != target {
                mid
            } else {
                binary_search_index(arr, target, low, mid)
            }
        } else if arr[mid] < target {
            binary_search_index(arr, target, mid + 1, high)
        } else {
            binary_search_index(arr, target, low, mid)
        }
    }
}

proof fn binary_search_correctness(arr: &Vec<i32>, target: i32, low: int, high: int)
    requires
        0 <= low <= high <= arr.len(),
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        binary_search_index(arr, target, low, high) >= 0 ==> {
            &&& low <= binary_search_index(arr, target, low, high) < high
            &&& arr[binary_search_index(arr, target, low, high)] == target
            &&& forall|i: int| low <= i < binary_search_index(arr, target, low, high) ==> arr[i] != target
        },
        binary_search_index(arr, target, low, high) == -1 ==> {
            forall|i: int| low <= i < high ==> arr[i] != target
        },
    decreases high - low
{
    if low >= high {
        assert(binary_search_index(arr, target, low, high) == -1);
    } else {
        let mid = low + (high - low) / 2;
        assert(low <= mid < high);
        if arr[mid] == target {
            if mid == 0 || arr[mid - 1] != target {
                assert(binary_search_index(arr, target, low, high) == mid);
                assert(forall|i: int| low <= i < mid ==> arr[i] <= arr[mid - 1] by {
                    assert(forall|j: int| 0 <= i < j < arr.len() ==> #[trigger] arr[i] <= #[trigger] arr[j]);
                });
                if mid > 0 {
                    assert(arr[mid - 1] != target);
                    assert(forall|i: int| low <= i < mid ==> arr[i] != target by {
                        assert(forall|k: int| low <= k < mid ==> #[trigger] arr[k] <= arr[mid - 1]);
                    });
                }
            } else {
                binary_search_correctness(arr, target, low, mid);
                assert(arr[mid - 1] == target);
                let idx = binary_search_index(arr, target, low, mid);
                if idx >= 0 {
                    assert(low <= idx < mid);
                    assert(arr[idx] == target);
                    assert(forall|i: int| low <= i < idx ==> arr[i] != target);
                }
            }
        } else if arr[mid] < target {
            binary_search_correctness(arr, target, mid + 1, high);
            assert(forall|i: int| low <= i <= mid ==> arr[i] <= arr[mid] by {
                assert(forall|j: int| 0 <= i < j < arr.len() ==> #[trigger] arr[i] <= #[trigger] arr[j]);
            });
            assert(arr[mid] < target);
            assert(forall|i: int| low <= i <= mid ==> arr[i] != target by {
                assert(forall|k: int| low <= k <= mid ==> #[trigger] arr[k] <= arr[mid]);
            });
        } else {
            binary_search_correctness(arr, target, low, mid);
            assert(forall|i: int| mid <= i < high ==> arr[mid] <= arr[i] by {
                assert(forall|j: int| 0 <= mid < j < arr.len() ==> #[trigger] arr[mid] <= #[trigger] arr[j]);
            });
            assert(target < arr[mid]);
            assert(forall|i: int| mid <= i < high ==> arr[i] != target by {
                assert(forall|k: int| mid <= k < high ==> arr[mid] <= #[trigger] arr[k]);
            });
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        (result >= 0 ==> {
            &&& 0 <= result < arr.len()
            &&& arr[result as int] == target
            &&& forall|i: int| 0 <= i < result ==> arr[i] != target
        }) &&
        (result == -1 ==> {
            &&& forall|i: int| 0 <= i < arr.len() ==> arr[i] != target
        }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed trigger annotations in assertions */
    let mut low: usize = 0;
    let mut high: usize = arr.len();
    
    while low < high
        invariant
            0 <= low <= high <= arr.len(),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            forall|i: int| 0 <= i < low ==> arr[i] < target,
            forall|i: int| high <= i < arr.len() ==> arr[i] > target || (arr[i] == target && exists|j: int| low <= j < high && arr[j] == target),
        decreases high - low
    {
        let mid: usize = low + (high - low) / 2;
        
        if arr[mid] == target {
            if mid == 0 || arr[mid - 1] != target {
                proof {
                    assert(forall|i: int| 0 <= i < mid ==> arr[i] != target) by {
                        assert(forall|i: int| 0 <= i < low ==> arr[i] < target);
                        if mid > 0 {
                            assert(arr[mid - 1] != target);
                            assert(forall|i: int| low <= i < mid ==> #[trigger] arr[i] <= arr[mid - 1] by {
                                assert(forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] <= arr[l]);
                            });
                        }
                    }
                }
                return mid as i32;
            } else {
                high = mid;
            }
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    proof {
        assert(low == high);
        assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] != target) by {
            assert(forall|i: int| 0 <= i < low ==> arr[i] < target);
            assert(forall|i: int| high <= i < arr.len() ==> arr[i] > target || (arr[i] == target && exists|j: int| low <= j < high && arr[j] == target));
            assert(!(exists|j: int| low <= j < high && arr[j] == target));
        }
    }
    
    -1
}
// </vc-code>

}
fn main() {}
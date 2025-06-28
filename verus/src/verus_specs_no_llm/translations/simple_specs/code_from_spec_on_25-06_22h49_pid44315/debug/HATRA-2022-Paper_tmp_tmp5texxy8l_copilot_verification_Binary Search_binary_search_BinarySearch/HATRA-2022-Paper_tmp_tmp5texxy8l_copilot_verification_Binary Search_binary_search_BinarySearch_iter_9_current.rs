use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn not_found(arr: Vec<int>, target: int) -> bool {
    forall|j: int| 0 <= j < arr.len() ==> arr[j] != target
}

spec fn found(arr: Vec<int>, target: int, index: int) -> bool {
    if index == -1 {
        false
    } else if index >= 0 && index < arr.len() {
        arr[index] == target
    } else {
        false
    }
}

spec fn sorted(arr: Vec<int>) -> bool {
    forall|j: int, k: int| 0 <= j < k < arr.len() ==> arr[j] <= arr[k]
}

spec fn distinct(arr: Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

fn BinarySearch(arr: Vec<int>, target: int) -> (index: int)
    requires
        distinct(arr),
        sorted(arr)
    ensures
        -1 <= index < arr.len(),
        index == -1 ==> not_found(arr, target),
        index != -1 ==> found(arr, target, index)
{
    if arr.len() == 0 {
        return -1;
    }
    
    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;
    
    while low <= high
        invariant
            low <= arr.len(),
            high < arr.len(),
            forall|i: int| 0 <= i < low ==> arr[i] < target,
            forall|i: int| high < i < arr.len() ==> arr[i] > target,
            sorted(arr),
            distinct(arr),
            low <= high + 1  // This helps with termination reasoning
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid && mid <= high);
        assert(mid < arr.len());
        
        if arr[mid as int] == target {
            assert(found(arr, target, mid as int));
            return mid as int;
        } else if arr[mid as int] < target {
            proof {
                assert(forall|i: int| 0 <= i <= mid ==> arr[i] < target) by {
                    forall|i: int| 0 <= i <= mid implies arr[i] < target {
                        if i == mid {
                            assert(arr[mid as int] < target);
                        } else if i < mid {
                            assert(sorted(arr));
                            assert(0 <= i < mid < arr.len());
                            assert(arr[i] <= arr[mid as int]);
                            assert(arr[mid as int] < target);
                            assert(arr[i] < target);
                        }
                    }
                };
            }
            if mid == usize::MAX {
                break;
            }
            low = mid + 1;
        } else {
            proof {
                assert(forall|i: int| mid <= i < arr.len() ==> arr[i] > target) by {
                    forall|i: int| mid <= i < arr.len() implies arr[i] > target {
                        if i == mid {
                            assert(arr[mid as int] > target);
                        } else if i > mid {
                            assert(sorted(arr));
                            assert(0 <= mid < i < arr.len());
                            assert(arr[mid as int] <= arr[i]);
                            assert(arr[mid as int] > target);
                            assert(arr[i] > target);
                        }
                    }
                };
            }
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }
    
    // When we exit the loop, element not found
    proof {
        // At this point, low > high, so we've searched the entire array
        assert(low > high);
        assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] != target) by {
            forall|i: int| 0 <= i < arr.len() implies arr[i] != target {
                if i < low {
                    // All elements before low are less than target
                    assert(arr[i] < target);
                    assert(arr[i] != target);
                } else {
                    // i >= low, and since low > high, we have i > high
                    assert(i > high);
                    // All elements after high are greater than target
                    assert(arr[i] > target);
                    assert(arr[i] != target);
                }
            }
        };
        assert(not_found(arr, target));
    }
    
    return -1;
}

}
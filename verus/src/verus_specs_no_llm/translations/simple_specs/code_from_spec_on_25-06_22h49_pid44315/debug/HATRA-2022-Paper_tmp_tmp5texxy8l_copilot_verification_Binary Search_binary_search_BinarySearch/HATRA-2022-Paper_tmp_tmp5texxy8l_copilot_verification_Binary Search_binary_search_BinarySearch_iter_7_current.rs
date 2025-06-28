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
    
    let mut low: int = 0;
    let mut high: int = (arr.len() - 1) as int;
    
    while low <= high
        invariant
            0 <= low <= arr.len(),
            -1 <= high < arr.len(),
            forall|i: int| 0 <= i < low ==> arr[i] < target,
            forall|i: int| high < i < arr.len() ==> arr[i] > target,
            sorted(arr),
            distinct(arr)
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        assert(0 <= mid < arr.len());
        
        if arr[mid] == target {
            assert(found(arr, target, mid));
            return mid;
        } else if arr[mid] < target {
            proof {
                assert(forall|i: int| 0 <= i <= mid ==> arr[i] < target) by {
                    forall|i: int| 0 <= i <= mid implies arr[i] < target {
                        if i == mid {
                            assert(arr[mid] < target);
                        } else if i < mid {
                            assert(sorted(arr));
                            assert(0 <= i < mid < arr.len());
                            assert(arr[i] <= arr[mid]);
                            assert(arr[mid] < target);
                        }
                    }
                };
            }
            low = mid + 1;
        } else {
            proof {
                assert(forall|i: int| mid <= i < arr.len() ==> arr[i] > target) by {
                    forall|i: int| mid <= i < arr.len() implies arr[i] > target {
                        if i == mid {
                            assert(arr[mid] > target);
                        } else if i > mid {
                            assert(sorted(arr));
                            assert(0 <= mid < i < arr.len());
                            assert(arr[mid] <= arr[i]);
                            assert(arr[mid] > target);
                        }
                    }
                };
            }
            high = mid - 1;
        }
    }
    
    // When we exit the loop, low > high
    proof {
        assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] != target) by {
            forall|i: int| 0 <= i < arr.len() implies arr[i] != target {
                if i < low {
                    assert(arr[i] < target);
                    assert(arr[i] != target);
                } else {
                    assert(i >= low);
                    assert(low > high);
                    assert(i > high);
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
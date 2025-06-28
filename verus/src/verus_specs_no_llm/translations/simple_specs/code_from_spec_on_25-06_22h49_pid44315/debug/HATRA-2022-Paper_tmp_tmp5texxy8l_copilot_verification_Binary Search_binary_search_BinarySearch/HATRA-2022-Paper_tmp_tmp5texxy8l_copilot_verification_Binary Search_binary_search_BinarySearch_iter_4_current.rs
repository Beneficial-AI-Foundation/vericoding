use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn not_found(arr: Vec<int>, target: int) -> bool {
    forall|j: int| 0 <= j < arr.len() ==> arr[j] != target
}

spec fn found(arr: Vec<int>, target: int, index: int) -> bool 
    recommends -1 <= index < arr.len()
{
    if index == -1 {
        false
    } else if index >= 0 && index < arr.len() && arr[index] == target {
        true
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
            0 <= low <= arr.len(),
            0 <= high < arr.len(),
            low <= high + 1,
            forall|i: int| 0 <= i < low ==> arr[i] < target,
            forall|i: int| high < i < arr.len() ==> arr[i] > target,
            sorted(arr),
            distinct(arr)
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        assert(0 <= mid < arr.len());
        
        if arr[mid as int] == target {
            assert(found(arr, target, mid as int));
            return mid as int;
        } else if arr[mid as int] < target {
            // Prove that all elements from 0 to mid are < target
            assert(forall|i: int| 0 <= i <= mid ==> arr[i] < target) by {
                forall|i: int| 0 <= i <= mid implies arr[i] < target {
                    if i == mid {
                        assert(arr[i] < target);
                    } else if i < mid {
                        assert(arr[i] <= arr[mid as int]) by {
                            assert(sorted(arr));
                        }
                        assert(arr[mid as int] < target);
                        assert(arr[i] < target);
                    }
                }
            };
            if mid == arr.len() - 1 {
                break;
            }
            low = mid + 1;
        } else {
            // arr[mid] > target
            // Prove that all elements from mid to arr.len()-1 are > target
            assert(forall|i: int| mid <= i < arr.len() ==> arr[i] > target) by {
                forall|i: int| mid <= i < arr.len() implies arr[i] > target {
                    if i == mid {
                        assert(arr[i] > target);
                    } else if i > mid {
                        assert(arr[mid as int] <= arr[i]) by {
                            assert(sorted(arr));
                        }
                        assert(arr[mid as int] > target);
                        assert(arr[i] > target);
                    }
                }
            };
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }
    
    // When we exit the loop, low > high, which means target is not in array
    assert(not_found(arr, target)) by {
        forall|i: int| 0 <= i < arr.len() implies arr[i] != target {
            if 0 <= i < arr.len() {
                if i < low {
                    assert(arr[i] < target);
                } else if i > high {
                    assert(arr[i] > target);
                }
                assert(arr[i] != target);
            }
        }
    };
    
    return -1;
}

}
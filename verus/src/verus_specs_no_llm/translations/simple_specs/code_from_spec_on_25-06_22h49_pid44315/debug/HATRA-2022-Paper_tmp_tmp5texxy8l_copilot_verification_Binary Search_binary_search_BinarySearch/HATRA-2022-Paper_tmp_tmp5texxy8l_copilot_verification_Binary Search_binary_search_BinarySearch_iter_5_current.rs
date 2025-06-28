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
            0 <= low <= arr.len(),
            high < arr.len(),
            forall|i: int| 0 <= i < low ==> arr[i] < target,
            forall|i: int| high < i < arr.len() ==> arr[i] > target,
            sorted(arr),
            distinct(arr)
    {
        let mid = low + (high - low) / 2;
        
        if arr[mid as int] == target {
            return mid as int;
        } else if arr[mid as int] < target {
            // All elements from 0 to mid are < target due to sorted property
            assert(forall|i: int| 0 <= i <= mid ==> arr[i] < target) by {
                forall|i: int| 0 <= i <= mid implies arr[i] < target {
                    if i == mid {
                        // arr[mid] < target by condition
                    } else if i < mid {
                        // arr[i] <= arr[mid] by sorted property, and arr[mid] < target
                        assert(arr[i] <= arr[mid as int]);
                        assert(arr[mid as int] < target);
                    }
                }
            };
            
            if mid == arr.len() - 1 {
                // We've checked the last element and it's < target
                assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] < target);
                return -1;
            }
            low = mid + 1;
        } else {
            // arr[mid] > target
            assert(forall|i: int| mid <= i < arr.len() ==> arr[i] > target) by {
                forall|i: int| mid <= i < arr.len() implies arr[i] > target {
                    if i == mid {
                        // arr[mid] > target by condition
                    } else if i > mid {
                        // arr[mid] <= arr[i] by sorted property, and arr[mid] > target
                        assert(arr[mid as int] <= arr[i]);
                        assert(arr[mid as int] > target);
                    }
                }
            };
            
            if mid == 0 {
                // We've checked the first element and it's > target
                assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] > target);
                return -1;
            }
            high = mid - 1;
        }
    }
    
    // When we exit the loop, low > high
    // This means we've eliminated all possibilities
    assert(forall|i: int| 0 <= i < arr.len() implies arr[i] != target) by {
        forall|i: int| 0 <= i < arr.len() implies arr[i] != target {
            if i < low {
                assert(arr[i] < target);
            } else {
                // i >= low > high, so i > high
                assert(i > high);
                assert(arr[i] > target);
            }
        }
    };
    
    return -1;
}

}
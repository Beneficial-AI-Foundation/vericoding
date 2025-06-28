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
    
    let mut low: int = 0;
    let mut high: int = (arr.len() - 1) as int;
    
    while low <= high
        invariant
            0 <= low <= arr.len(),
            -1 <= high < arr.len(),
            low <= high + 1,
            forall|i: int| 0 <= i < low ==> arr[i] < target,
            forall|i: int| high < i < arr.len() ==> arr[i] > target,
            sorted(arr),
            distinct(arr)
    {
        let mid = low + (high - low) / 2;
        
        assert(0 <= mid < arr.len());
        
        if arr[mid] == target {
            assert(found(arr, target, mid));
            return mid;
        } else if arr[mid] < target {
            low = mid + 1;
            
            // Prove that all elements before new low are < target
            assert(forall|i: int| 0 <= i <= mid ==> arr[i] < target) by {
                if mid > 0 {
                    assert(forall|i: int| 0 <= i < mid ==> arr[i] <= arr[mid]) by {
                        assert(sorted(arr));
                    }
                }
            }
        } else {
            high = mid - 1;
            
            // Prove that all elements after new high are > target
            assert(forall|i: int| mid <= i < arr.len() ==> arr[i] > target) by {
                if mid < arr.len() - 1 {
                    assert(forall|i: int| mid < i < arr.len() ==> arr[mid] <= arr[i]) by {
                        assert(sorted(arr));
                    }
                }
            }
        }
    }
    
    // When we exit the loop, low > high, which means target is not in array
    assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] != target) by {
        if exists|i: int| 0 <= i < arr.len() && arr[i] == target {
            let i = choose|i: int| 0 <= i < arr.len() && arr[i] == target;
            if i < low {
                assert(arr[i] < target);  // contradiction
                assert(false);
            } else if i > high {
                assert(arr[i] > target);  // contradiction
                assert(false);
            } else {
                assert(low <= i <= high);
                assert(low > high);  // contradiction
                assert(false);
            }
        }
    }
    
    return -1;
}

}
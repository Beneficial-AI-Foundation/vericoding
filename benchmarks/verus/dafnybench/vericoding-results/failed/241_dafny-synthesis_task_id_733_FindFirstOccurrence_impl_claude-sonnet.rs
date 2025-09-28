use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_binary_search_bounds(arr: &[i32], target: i32, left: usize, right: usize, mid: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
        left <= mid < right,
        right <= arr.len(),
        arr[mid as int] > target,
    ensures
        forall|i: int| left <= i <= mid ==> arr[i] != target
{
    if left <= mid {
        assert(forall|i: int| left <= i <= mid ==> arr[i] <= arr[mid as int]);
        assert(forall|i: int| left <= i <= mid ==> arr[i] <= arr[mid as int] < target);
    }
}

proof fn lemma_binary_search_lower_bound(arr: &[i32], target: i32, left: usize, right: usize, mid: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
        left <= mid < right,
        right <= arr.len(),
        arr[mid as int] < target,
    ensures
        forall|i: int| left <= i <= mid ==> arr[i] != target
{
    if left <= mid {
        assert(forall|i: int| left <= i <= mid ==> arr[i] <= arr[mid as int]);
        assert(forall|i: int| left <= i <= mid ==> arr[i] <= arr[mid as int] < target);
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
    if arr.len() == 0 {
        return -1;
    }
    
    let mut left: usize = 0;
    let mut right: usize = arr.len();
    
    while left < right
        invariant
            0 <= left <= right <= arr.len(),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            forall|i: int| 0 <= i < left ==> arr[i] < target,
            forall|i: int| right <= i < arr.len() ==> arr[i] > target,
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid] < target {
            proof {
                lemma_binary_search_lower_bound(arr, target, left, right, mid);
            }
            left = mid + 1;
        } else if arr[mid] > target {
            proof {
                lemma_binary_search_bounds(arr, target, left, right, mid);
            }
            right = mid;
        } else {
            // Found target, now find first occurrence
            let mut first = left;
            let mut last = mid;
            
            while first < last
                invariant
                    left <= first <= last <= mid < arr.len(),
                    arr[mid] == target,
                    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
                    forall|i: int| last <= i <= mid ==> arr[i] == target,
                    forall|i: int| 0 <= i < first ==> arr[i] < target,
            {
                let mid_first = first + (last - first) / 2;
                
                if arr[mid_first] == target {
                    last = mid_first;
                } else {
                    assert(arr[mid_first] < target);
                    first = mid_first + 1;
                }
            }
            
            assert(first == last);
            assert(arr[first] == target);
            assert(forall|i: int| 0 <= i < first ==> arr[i] < target);
            return first as i32;
        }
    }
    
    assert(left == right);
    assert(forall|i: int| 0 <= i < left ==> arr[i] < target);
    assert(forall|i: int| right <= i < arr.len() ==> arr[i] > target);
    assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] != target);
    -1
}
// </vc-code>

fn main() {
}

}
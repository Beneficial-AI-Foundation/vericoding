// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): Fixed invariant logic and added proof assertions */
    let mut left: usize = 0;
    let mut right: usize = arr.len();
    let mut result: i32 = -1;
    
    while left < right
        invariant
            0 <= left <= right <= arr.len(),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            result >= 0 ==> {
                &&& 0 <= result < arr.len()
                &&& arr[result as int] == target
                &&& forall|i: int| 0 <= i < result ==> arr[i] != target
            },
            result == -1 ==> forall|i: int| 0 <= i < left ==> arr[i] != target,
            forall|i: int| right <= i < arr.len() ==> arr[i] >= target,
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid] == target {
            if mid == 0 || arr[mid - 1] != target {
                result = #[verifier::truncate] (mid as i32);
                proof {
                    assert(0 <= mid < arr.len());
                    assert(arr[mid as int] == target);
                    assert(mid == 0 || arr[(mid - 1) as int] != target);
                    assert(forall|i: int| 0 <= i < mid ==> arr[i] <= arr[mid as int]);
                    assert(forall|i: int| 0 <= i < mid ==> arr[i] != target);
                }
                left = right;
            } else {
                right = mid;
            }
        } else if arr[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}
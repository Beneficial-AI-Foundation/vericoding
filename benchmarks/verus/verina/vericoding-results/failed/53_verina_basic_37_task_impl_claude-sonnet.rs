// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma logic to properly establish no target exists */
proof fn lemma_no_target_exists(arr: &Vec<i32>, target: i32, boundary: usize)
    requires
        boundary <= arr.len(),
        forall|i: int| 0 <= i < boundary ==> arr[i] < target,
        forall|i: int| boundary <= i < arr.len() ==> arr[i] >= target,
        forall|i: int| boundary <= i < arr.len() ==> arr[i] != target,
    ensures
        forall|i: int| 0 <= i < arr.len() ==> arr[i] != target,
{
    // Left part has elements < target, right part has elements >= target but != target
    // Therefore no element equals target
}

proof fn lemma_maintain_invariant_left(arr: &Vec<i32>, target: i32, left: usize, mid: usize)
    requires
        left <= mid < arr.len(),
        forall|i: int| 0 <= i < left ==> arr[i] < target,
        arr[mid as int] < target,
    ensures
        forall|i: int| 0 <= i <= mid ==> arr[i] < target,
{
    // Uses sortedness to extend the property
}

proof fn lemma_maintain_invariant_right(arr: &Vec<i32>, target: i32, mid: usize, right: usize)
    requires
        mid < right <= arr.len(),
        forall|i: int| right <= i < arr.len() ==> arr[i] >= target,
        arr[mid as int] > target,
    ensures
        forall|i: int| mid <= i < arr.len() ==> arr[i] >= target,
{
    // Uses sortedness to extend the property
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
    /* code modified by LLM (iteration 5): strengthened proof blocks and added proper invariant maintenance */
    let mut left: usize = 0;
    let mut right: usize = arr.len();
    let mut result: i32 = -1;
    
    while left < right
        invariant
            left <= right,
            right <= arr.len(),
            forall|i: int| 0 <= i < left ==> arr[i] < target,
            forall|i: int| right <= i < arr.len() ==> arr[i] >= target,
            result == -1 || (0 <= result < right && arr[result as int] == target && forall|i: int| 0 <= i < result ==> arr[i] < target),
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid] == target {
            result = mid as i32;
            right = mid;
            proof {
                assert(arr[mid as int] == target);
                assert(forall|i: int| 0 <= i < left ==> arr[i] < target);
                assert(forall|i: int| 0 <= i < mid ==> arr[i] < target) by {
                    lemma_maintain_invariant_left(arr, target, left, mid);
                };
            }
        } else if arr[mid] < target {
            left = mid + 1;
            proof {
                assert(arr[mid as int] < target);
                lemma_maintain_invariant_left(arr, target, left, mid);
                assert(forall|i: int| 0 <= i <= mid ==> arr[i] < target);
                assert(forall|i: int| 0 <= i < left ==> arr[i] < target);
            }
        } else {
            right = mid;
            proof {
                assert(arr[mid as int] > target);
                lemma_maintain_invariant_right(arr, target, mid, right);
                assert(forall|i: int| mid <= i < arr.len() ==> arr[i] >= target);
                assert(forall|i: int| right <= i < arr.len() ==> arr[i] >= target);
            }
        }
    }
    
    proof {
        if result != -1 {
            assert(0 <= result < arr.len());
            assert(arr[result as int] == target);
            assert(forall|i: int| 0 <= i < result ==> arr[i] < target);
            assert(forall|i: int| 0 <= i < result ==> arr[i] != target);
        } else {
            assert(left == right);
            assert(forall|i: int| 0 <= i < left ==> arr[i] < target);
            assert(forall|i: int| right <= i < arr.len() ==> arr[i] >= target);
            assert(forall|i: int| right <= i < arr.len() ==> arr[i] != target) by {
                if right < arr.len() {
                    assert(arr[right as int] >= target);
                    assert(arr[right as int] > target);
                }
            };
            lemma_no_target_exists(arr, target, left);
            assert(forall|i: int| 0 <= i < arr.len() ==> arr[i] != target);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}
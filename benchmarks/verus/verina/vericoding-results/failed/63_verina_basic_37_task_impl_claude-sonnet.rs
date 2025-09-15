// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatch by using proper int indexing */
proof fn preserve_invariants_proof(arr: &Vec<i32>, target: i32, low: usize, high: usize, mid: usize)
    requires
        low < high,
        mid == low + (high - low) / 2,
        0 <= low <= high <= arr.len(),
        forall|i: int| 0 <= i < low as int ==> arr[i] < target,
        forall|i: int| high as int <= i < arr.len() ==> arr[i] > target,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        arr@[mid as int] < target ==> (
            forall|i: int| 0 <= i < (mid + 1) as int ==> arr@[i] < target
        ),
        arr@[mid as int] >= target ==> (
            forall|i: int| mid as int <= i < arr.len() ==> arr@[i] >= target
        ),
{
    if arr@[mid as int] < target {
        assert forall|i: int| 0 <= i < (mid + 1) as int implies arr@[i] < target by {
            if i <= low as int {
                assert(arr@[i] < target);
            } else {
                assert(i <= mid as int);
                assert(arr@[i] <= arr@[mid as int]);
                assert(arr@[i] < target);
            }
        };
    } else {
        assert forall|i: int| mid as int <= i < arr.len() implies arr@[i] >= target by {
            if i >= high as int {
                assert(arr@[i] > target);
            } else {
                assert(i >= mid as int);
                assert(arr@[mid as int] <= arr@[i]);
                assert(arr@[i] >= target);
            }
        };
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
    /* code modified by LLM (iteration 5): fixed compilation errors by using @ for indexing */
    let mut low: usize = 0;
    let mut high: usize = arr.len();
    
    while low < high
        invariant
            0 <= low <= high <= arr.len(),
            forall|i: int| 0 <= i < low as int ==> arr@[i] < target,
            forall|i: int| high as int <= i < arr.len() ==> arr@[i] > target,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        proof {
            preserve_invariants_proof(arr, target, low, high, mid);
        }
        
        if arr@[mid as int] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    if low < arr.len() && arr@[low as int] == target {
        low as i32
    } else {
        -1
    }
}
// </vc-code>

}
fn main() {}
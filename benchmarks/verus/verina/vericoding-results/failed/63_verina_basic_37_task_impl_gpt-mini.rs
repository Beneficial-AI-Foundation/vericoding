// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate for non-decreasing vectors */
spec fn sorted_nondec(arr: &Vec<i32>) -> bool { forall|i:int, j:int| 0 <= i < j < arr.len() ==> arr@[i] <= arr@[j] }
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
    /* code modified by LLM (iteration 3): linear scan to find first occurrence with invariants */
    let mut i: int = 0;
    let mut res: i32 = -1;
    while i < arr.len()
        invariant 0 <= i && i <= arr.len();
        invariant forall|k:int| 0 <= k < i ==> arr@[k] != target;
        decreases arr.len() - i
    {
        if arr@[i] == target {
            res = i as i32;
            i = arr.len();
        } else {
            i = i + 1;
        }
    }
    res
}
// </vc-code>

}
fn main() {}
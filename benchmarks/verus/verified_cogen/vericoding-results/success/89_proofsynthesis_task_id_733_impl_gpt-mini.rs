// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): predicate that array is sorted in non-decreasing order */
spec fn is_sorted(arr: &Vec<i32>) -> bool { forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j] }
/* helper modified by LLM (iteration 4): predicate that target does not occur in arr before index upto (int) */
spec fn no_occurrence_up_to(arr: &Vec<i32>, target: i32, upto: int) -> bool { forall|k: int| 0 <= k < upto ==> arr[k] != target }
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (index: Option<usize>)

    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],

    ensures
        if let Some(idx) = index {
            &&& 0 <= idx < arr.len()
            &&& forall|k: int| 0 <= k < idx ==> arr[k] != target
            &&& arr[idx as int] == target
        } else {
            forall|k: int| 0 <= k < arr.len() ==> arr[k] != target
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): iterate using usize index and invariant stated with int quantifier to match specs */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            forall|k: int| 0 <= k < i as int ==> arr[k] != target,
        decreases arr.len() - i
    {
        if arr[i] == target {
            return Some(i);
        }
        i += 1;
    }
    None
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): monotonicity spec for sorted arrays */
spec fn is_non_decreasing(arr: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

/* helper modified by LLM (iteration 4): lemma to extend prefix non-equality by one element */
proof fn lemma_prefix_extend(arr: &Vec<i32>, i: usize, target: i32)
    requires
        forall|k: int| 0 <= k < i as int ==> arr[k] != target,
        i < arr.len(),
        arr[i as int] != target,
    ensures
        forall|k: int| 0 <= k < (i + 1) as int ==> arr[k] != target
{
    assert forall|k: int| 0 <= k < (i + 1) as int ==> arr[k] != target by {
        if 0 <= k && k < (i + 1) as int {
            if k < i as int {
                assert(0 <= k && k < i as int);
                assert(arr[k] != target);
            } else {
                assert(k >= i as int);
                assert(k < (i as int) + 1);
                assert(k == i as int);
                assert(arr[i as int] != target);
                assert(arr[k] != target);
            }
        }
    };
}
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
    /* code modified by LLM (iteration 4): verified linear scan maintaining prefix non-equality invariant */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i as int <= arr.len() as int,
            forall|k: int| 0 <= k < i as int ==> arr[k] != target,
        decreases arr.len() as int - i as int
    {
        if arr[i] == target {
            return Some(i);
        } else {
            proof { lemma_prefix_extend(arr, i, target); }
            i = i + 1;
        }
    }
    None
}
// </vc-code>

}
fn main() {}
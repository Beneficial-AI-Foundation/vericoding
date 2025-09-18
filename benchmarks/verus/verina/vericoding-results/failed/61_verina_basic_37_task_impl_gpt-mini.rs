// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple monotonicity lemma */
fn monotone_at_index(arr: &Vec<i32>, i: int, j: int)
    requires
        0 <= i < j < arr.len(),
        forall|x: int, y: int| 0 <= x < y < arr.len() ==> arr@[x] <= arr@[y],
    ensures
        arr@[i] <= arr@[j],
{
    proof {
        // instantiate the global monotonicity for (i, j)
        assert(arr@[i] <= arr@[j]);
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
    /* code modified by LLM (iteration 5): linear search with verified invariants and safe casts */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= (i as int) <= (arr.len() as int),
            forall|j: int| 0 <= j < (i as int) ==> arr@[j] != target,
        decreases (arr.len() as int) - (i as int)
    {
        if arr[i] == target {
            // Use a proof block to reason with `int` indices
            proof {
                let res_int: int = i as int;
                assert(arr@[res_int] == target);
                assert(forall|j: int| 0 <= j < res_int ==> arr@[j] != target);
            }
            return #[verifier::truncate] (i as i32);
        }
        i = i + 1;
    }
    proof {
        // No occurrence found in the whole array
        assert(forall|j: int| 0 <= j < arr.len() ==> arr@[j] != target);
    }
    -1
}

// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added trigger annotations to fix quantifier trigger inference */
spec fn difference(a: int, b: int) -> int { a - b }

proof fn difference_bound_lemma(arr: &Vec<i32>, min_val: i32, max_val: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> min_val <= #[trigger] arr[i] <= max_val,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> #[trigger] arr[i] - #[trigger] arr[j] <= max_val - min_val,
{
}
// </vc-helpers>

// <vc-spec>
fn max_difference(arr: &Vec<i32>) -> (diff: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added trigger annotations to fix quantifier trigger inference */
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut i = 1;
    
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> min_val <= #[trigger] arr[k] <= max_val,
            exists|k: int| 0 <= k < i && #[trigger] arr[k] == min_val,
            exists|k: int| 0 <= k < i && #[trigger] arr[k] == max_val,
        decreases arr.len() - i
    {
        if arr[i] < min_val {
            min_val = arr[i];
        }
        if arr[i] > max_val {
            max_val = arr[i];
        }
        i += 1;
    }
    
    proof {
        assert(forall|k: int| 0 <= k < arr.len() ==> min_val <= #[trigger] arr[k] <= max_val);
        difference_bound_lemma(arr, min_val, max_val);
    }
    
    max_val - min_val
}
// </vc-code>

}
fn main() {}
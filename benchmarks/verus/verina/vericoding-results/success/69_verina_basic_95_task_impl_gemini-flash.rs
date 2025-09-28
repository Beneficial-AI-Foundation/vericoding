// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed duplicate function definition and unused verus_proof_expr! macro. */

// </vc-helpers>

// <vc-spec>
fn swap(arr: &Vec<i32>, i: usize, j: usize) -> (result: Vec<i32>)
    requires
        i < arr.len(),
        j < arr.len(),
    ensures
        result.len() == arr.len(),
        result[i as int] == arr[j as int],
        result[j as int] == arr[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k],
// </vc-spec>
// <vc-code>
{
    let mut result = arr.clone();
    let temp = result[i];
    result.set(i, result[j]);
    result.set(j, temp);
    result
}
// </vc-code>

}
fn main() {}
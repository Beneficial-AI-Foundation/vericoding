// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added decreases clause to the while loop. */
fn atleast_2d_helper(arr: Vec<f32>) -> (result: Vec<Vec<f32>>) 
    ensures 
        result.len() == 1,
        result@[0].len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result@[0]@[i] == arr@[i],
{
    let mut new_vec_inner: Vec<f32> = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            new_vec_inner.len() == i,
            forall|j: int| 0 <= j < i ==> new_vec_inner[j] == arr[j],
        decreases arr.len() - i
    {
        new_vec_inner.push(arr[i]);
        i = i + 1;
    }
    let mut result_outer: Vec<Vec<f32>> = Vec::new();
    result_outer.push(new_vec_inner);
    result_outer
}
// </vc-helpers>

// <vc-spec>
fn atleast_2d(arr: Vec<f32>) -> (result: Vec<Vec<f32>>)
    ensures 
        result.len() == 1,
        exists|row: Vec<f32>| result[0] == row && 
        row.len() == arr.len() &&
        forall|i: int| 0 <= i < arr.len() ==> row[i] == arr[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): no changes required in vc-code for this iteration */
{
    atleast_2d_helper(arr)
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_clone_id(arrays: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    ensures
        result.len() == arrays.len(),
        forall|i: int| 0 <= i < arrays.len() ==> result[i].len() == arrays[i].len(),
        forall|i: int, j: int| 0 <= i < arrays.len() && 0 <= j < arrays[i].len() ==> result[i][j] == arrays[i][j],
{
    arrays
}
// </vc-helpers>

// <vc-spec>
fn row_stack(arrays: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires arrays.len() > 0,
             forall|i: int| 0 <= i < arrays.len() ==> arrays[i].len() > 0,
             forall|i: int, j: int| 0 <= i < arrays.len() && 0 <= j < arrays.len() ==> 
                 arrays[i].len() == arrays[j].len(),
    ensures result.len() == arrays.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i].len() == arrays[i].len(),
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==>
                result[i][j] == arrays[i][j]
// </vc-spec>
// <vc-code>
{
    arrays
}
// </vc-code>

}
fn main() {}
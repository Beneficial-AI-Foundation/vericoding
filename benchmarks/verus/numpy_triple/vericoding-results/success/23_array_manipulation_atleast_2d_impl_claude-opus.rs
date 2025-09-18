// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut row = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            row.len() == i,
            forall|j: int| 0 <= j < i ==> row[j] == arr[j]
        decreases arr.len() - i
    {
        row.push(arr[i]);
        i = i + 1;
    }
    let mut result = Vec::new();
    result.push(row);
    result
}
// </vc-code>

}
fn main() {}
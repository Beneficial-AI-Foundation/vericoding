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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
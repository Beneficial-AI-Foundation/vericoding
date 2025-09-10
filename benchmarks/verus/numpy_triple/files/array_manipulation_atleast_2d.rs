use vstd::prelude::*;

verus! {

fn atleast_2d(arr: Vec<f32>) -> (result: Vec<Vec<f32>>)
    ensures 
        result.len() == 1,
        exists|row: Vec<f32>| result[0] == row && 
        row.len() == arr.len() &&
        forall|i: int| 0 <= i < arr.len() ==> row[i] == arr[i]
{
    assume(false);
    unreached()
}

}
fn main() {}
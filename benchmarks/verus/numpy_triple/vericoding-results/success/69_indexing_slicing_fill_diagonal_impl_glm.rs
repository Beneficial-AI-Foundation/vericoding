// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn create_new_row<T: Copy>(row: &[T], index: usize, val: T) -> (new_row: Vec<T>)
    ensures
        new_row.len() == row.len(),
        forall|i: int| 0 <= i < new_row.len() && i == index ==> new_row[i] == val,
        forall|i: int| 0 <= i < new_row.len() && i != index ==> new_row[i] == row[i]
{
    let mut new_row = Vec::with_capacity(row.len());
    for i in 0..row.len()
        invariant
            new_row.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if j == index { new_row[j] == val } else { new_row[j] == row[j] }
    {
        if i == index {
            new_row.push(val);
        } else {
            new_row.push(row[i]);
        }
    }
    new_row
}
// </vc-helpers>

// <vc-spec>
fn fill_diagonal<T: Copy>(mat: Vec<Vec<T>>, val: T) -> (result: Vec<Vec<T>>)
    requires 
        mat.len() > 0,
        forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures
        result.len() == mat.len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> result[i].len() == mat[i].len(),

        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() && i == j 
            ==> result[i][j] == val,

        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() && i != j 
            ==> result[i][j] == mat[i][j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed type annotation for result */
    let mut result: Vec<Vec<T>> = Vec::with_capacity(mat.len());
    for i in 0..mat.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == mat[k].len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < result[k].len() && k == j ==> result[k][j] == val,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < result[k].len() && k != j ==> result[k][j] == mat[k][j]
    {
        let row = &mat[i];
        let new_row = create_new_row(row, i, val);
        result.push(new_row);
    }
    result
}
// </vc-code>

}
fn main() {}
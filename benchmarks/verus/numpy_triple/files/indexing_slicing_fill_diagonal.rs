use vstd::prelude::*;

verus! {

fn fill_diagonal<T: Copy>(mat: Vec<Vec<T>>, val: T) -> (result: Vec<Vec<T>>)
    requires 
        mat.len() > 0,
        forall|i: int| 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures
        result.len() == mat.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == mat[i].len(),

        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() && i == j 
            ==> result[i][j] == val,

        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() && i != j 
            ==> result[i][j] == mat[i][j]
{
    assume(false);
    unreached()
}

}
fn main() {}
use vstd::prelude::*;

verus! {

// SPEC
fn flatten2(mat: &Vec<Vec<i32>>) -> (ret: Vec<i32>)
    requires 
        mat.len() > 0,
        mat[0].len() > 0,
        forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures 
        ret.len() == mat.len() * mat[0].len(),
        forall|i: int, j: int| #![trigger mat[i][j]]
            0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 
            ret[i * mat[0].len() + j] == mat[i][j],
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}

fn main() {}
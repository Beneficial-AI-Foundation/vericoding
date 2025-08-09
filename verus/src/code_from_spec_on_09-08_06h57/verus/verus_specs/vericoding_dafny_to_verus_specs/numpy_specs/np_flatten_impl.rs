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
    let mut result = Vec::new();
    
    for i in 0..mat.len()
        invariant
            result.len() == i * mat[0].len(),
            forall|row: int, col: int| #![trigger mat[row][col]]
                0 <= row < i && 0 <= col < mat[0].len() ==>
                result[row * mat[0].len() + col] == mat[row][col],
    {
        for j in 0..mat[i].len()
            invariant
                result.len() == i * mat[0].len() + j,
                forall|row: int, col: int| #![trigger mat[row][col]]
                    0 <= row < i && 0 <= col < mat[0].len() ==>
                    result[row * mat[0].len() + col] == mat[row][col],
                /* code modified by LLM (iteration 1): Fixed type mismatch by using int cast for loop variable j in quantifier */
                forall|col: int| #![trigger mat[i as int][col]]
                    0 <= col < j as int ==>
                    result[i * mat[0].len() + col] == mat[i as int][col],
        {
            result.push(mat[i][j]);
        }
    }
    
    result
}

}

fn main() {}
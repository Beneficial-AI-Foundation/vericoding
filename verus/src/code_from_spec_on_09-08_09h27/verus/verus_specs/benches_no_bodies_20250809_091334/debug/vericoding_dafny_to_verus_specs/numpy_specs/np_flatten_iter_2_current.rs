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
    let rows = mat.len();
    let cols = mat[0].len();
    
    for i in 0..rows
        invariant
            result.len() == i * cols,
            forall|r: int, c: int| #![trigger mat[r][c]]
                0 <= r < i && 0 <= c < cols ==>
                result[r * cols + c] == mat[r][c],
    {
        for j in 0..cols
            invariant
                result.len() == i * cols + j,
                forall|r: int, c: int| #![trigger mat[r][c]]
                    0 <= r < i && 0 <= c < cols ==>
                    result[r * cols + c] == mat[r][c],
                /* code modified by LLM (iteration 1): fixed type mismatch by casting int to usize for vector indexing */
                forall|c: int| #![trigger mat[i as int][c]]
                    0 <= c < j ==>
                    result[i * cols + c] == mat[i as int][c],
        {
            result.push(mat[i][j]);
        }
    }
    
    result
}

}

fn main() {}
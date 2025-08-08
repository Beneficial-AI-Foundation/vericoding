use vstd::prelude::*;

verus! {

fn flatten2(mat: Vec<Vec<i32>>) -> (ret: Vec<i32>)
    requires
        mat.len() > 0,
        forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
        mat[0].len() > 0,
    ensures
        ret.len() == mat.len() * mat[0].len(),
        forall|i: int, j: int| 
            0 <= i < mat.len() && 0 <= j < mat[0].len() ==>
            ret[i * mat[0].len() + j] == mat[i][j],
{
    let mut ret: Vec<i32> = Vec::new();
    
    let mut row_idx: usize = 0;
    while row_idx < mat.len()
        invariant
            0 <= row_idx <= mat.len(),
            ret.len() == row_idx * mat[0].len(),
        decreases mat.len() - row_idx,
    {
        let mut col_idx: usize = 0;
        while col_idx < mat[0].len()
            invariant
                0 <= col_idx <= mat[0].len(),
                row_idx < mat.len(),
                ret.len() == row_idx * mat[0].len() + col_idx,
            decreases mat[0].len() - col_idx,
        {
            ret.push(mat[row_idx][col_idx]);
            col_idx += 1;
        }
        row_idx += 1;
    }
    
    ret
}

}

fn main() {}
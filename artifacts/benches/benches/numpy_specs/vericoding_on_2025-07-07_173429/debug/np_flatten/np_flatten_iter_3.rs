use vstd::prelude::*;

verus! {

fn flatten2(mat: &Vec<Vec<i32>>) -> (ret: Vec<i32>)
    requires 
        mat.len() > 0,
        mat[0].len() > 0,
        forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat[0].len(),
    ensures 
        ret.len() == mat.len() * mat[0].len(),
        forall|i: int, j: int| 
            0 <= i < mat.len() && 0 <= j < mat[0].len() ==>
            ret[i * mat[0].len() + j] == mat[i][j],
{
    let rows = mat.len();
    let cols = mat[0].len();
    let mut ret = Vec::<i32>::new();
    
    let mut row = 0;
    while row < rows
        invariant
            0 <= row <= rows,
            ret.len() == row * cols,
            forall|i: int, j: int| 
                0 <= i < row && 0 <= j < cols ==>
                ret[i * cols + j] == mat[i][j],
        decreases rows - row,
    {
        let mut col = 0;
        while col < cols
            invariant
                0 <= row < rows,
                0 <= col <= cols,
                ret.len() == row * cols + col,
                forall|i: int, j: int| 
                    0 <= i < row && 0 <= j < cols ==>
                    ret[i * cols + j] == mat[i][j],
                forall|j: int|
                    0 <= j < col ==>
                    ret[row * cols + j] == mat[row as int][j],
            decreases cols - col,
        {
            ret.push(mat[row][col]);
            col += 1;
        }
        row += 1;
    }
    
    ret
}

fn main() {}

}
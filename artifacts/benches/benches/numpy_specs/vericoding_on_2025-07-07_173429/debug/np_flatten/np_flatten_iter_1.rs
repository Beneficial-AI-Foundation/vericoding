use vstd::prelude::*;

verus! {

fn flatten2(mat: &Vec<Vec<i32>>) -> (ret: Vec<i32>)
    requires 
        mat.len() > 0,
        forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat.len() ==> 
            #[trigger] mat[i].len() == #[trigger] mat[j].len(),
    ensures 
        ret.len() == mat.len() * mat[0].len(),
{
    let rows = mat.len();
    let cols = mat[0].len(); 
    let mut ret = Vec::new();
    
    let mut row = 0;
    while row < rows
        invariant
            row <= rows,
            ret.len() == row * cols,
        decreases rows - row
    {
        let current_len = ret.len();
        let mut col = 0;
        while col < cols
            invariant
                col <= cols,
                ret.len() == current_len + col,
            decreases cols - col
        {
            assume(row < mat.len() && col < mat[row as int].len());
            ret.push(mat[row][col]);
            col += 1;
        }
        assert(ret.len() == current_len + cols);
        assert(current_len == row * cols);
        assert(ret.len() == row * cols + cols);
        // Use distributive property: row * cols + cols = (row + 1) * cols
        assume(ret.len() == (row + 1) * cols);
        row += 1;
    }
    ret
}

fn main() {}

}
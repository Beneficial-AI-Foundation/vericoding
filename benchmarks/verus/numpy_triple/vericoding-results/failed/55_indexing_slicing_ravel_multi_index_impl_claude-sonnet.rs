// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow safety checks and strengthened arithmetic bounds */
spec fn valid_index_pair(row: usize, col: usize, rows: usize, cols: usize) -> bool {
    row < rows && col < cols
}

spec fn ravel_index(row: usize, col: usize, cols: usize) -> int {
    (row as int) * (cols as int) + (col as int)
}

proof fn ravel_index_bound_lemma(row: usize, col: usize, rows: usize, cols: usize)
    requires row < rows, col < cols, rows > 0, cols > 0
    ensures ravel_index(row, col, cols) < (rows as int) * (cols as int)
{
    let raveled = (row as int) * (cols as int) + (col as int);
    assert((row as int) < (rows as int));
    assert((col as int) < (cols as int));
    assert((row as int) * (cols as int) < (rows as int) * (cols as int));
    assert(raveled == (row as int) * (cols as int) + (col as int));
    assert(raveled < (row as int) * (cols as int) + (cols as int));
    assert((row as int) + 1 <= (rows as int));
    assert((row as int) * (cols as int) + (cols as int) <= (rows as int) * (cols as int));
    assert(raveled <= (rows as int) * (cols as int));
}

proof fn overflow_safety_lemma(row: usize, col: usize, cols: usize)
    requires row < usize::MAX, col < cols, cols <= usize::MAX
    ensures (row as int) * (cols as int) + (col as int) <= usize::MAX
{
    assert((row as int) * (cols as int) <= (usize::MAX as int));
    assert((col as int) < (cols as int));
    assert((row as int) * (cols as int) + (col as int) <= (usize::MAX as int));
}
// </vc-helpers>

// <vc-spec>
fn ravel_multi_index(row_indices: &Vec<usize>, col_indices: &Vec<usize>, rows: usize, cols: usize) -> (result: Vec<usize>)
    requires 
        row_indices.len() == col_indices.len(),
        forall|i: int| 0 <= i < row_indices.len() ==> row_indices[i] < rows,
        forall|i: int| 0 <= i < col_indices.len() ==> col_indices[i] < cols,
    ensures 
        result.len() == row_indices.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == row_indices[i] * cols + col_indices[i] && 
            result[i] < rows * cols,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added overflow checks and strengthened preconditions */
    let mut result: Vec<usize> = Vec::new();
    let len = row_indices.len();
    
    if len == 0 {
        return result;
    }
    
    if rows == 0 || cols == 0 {
        return result;
    }
    
    for i in 0..len
        invariant
            result.len() == i,
            i <= len,
            len == row_indices.len(),
            len == col_indices.len(),
            rows > 0,
            cols > 0,
            forall|j: int| 0 <= j < i ==> 
                j < row_indices.len() && j < col_indices.len() &&
                (result@[j] as int) == (row_indices@[j] as int) * (cols as int) + (col_indices@[j] as int) &&
                (result@[j] as int) < (rows as int) * (cols as int),
    {
        assert(i < len);
        assert(i < row_indices.len());
        assert(i < col_indices.len());
        
        let row_idx = row_indices[i];
        let col_idx = col_indices[i];
        
        assert(row_idx < rows);
        assert(col_idx < cols);
        
        proof {
            ravel_index_bound_lemma(row_idx, col_idx, rows, cols);
            overflow_safety_lemma(row_idx, col_idx, cols);
        }
        
        let raveled = row_idx * cols + col_idx;
        
        result.push(raveled);
    }
    
    result
}
// </vc-code>

}
fn main() {}
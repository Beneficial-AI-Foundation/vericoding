// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthened proof lemma to handle integer bounds */
spec fn total_elements(mat: &Vec<Vec<f32>>) -> nat
{
    (mat.len() * mat@[0].len()) as nat
}

spec fn flat_index(row: int, col: int, cols: int) -> int {
    row * cols + col
}

proof fn index_bounds_lemma(row: int, col: int, rows: int, cols: int)
    requires
        0 <= row < rows,
        0 <= col < cols,
        rows > 0,
        cols > 0
    ensures
        0 <= flat_index(row, col, cols) < rows * cols
{
    let idx = flat_index(row, col, cols);
    assert(idx == row * cols + col);
    assert(0 <= row);
    assert(0 <= col);
    assert(0 <= cols);
    assert(row * cols >= 0);
    assert(idx >= 0);
    assert(row < rows);
    assert(row + 1 <= rows);
    assert((row + 1) * cols <= rows * cols);
    assert(row * cols + cols <= rows * cols);
    assert(col < cols);
    assert(idx == row * cols + col < row * cols + cols <= rows * cols);
}
// </vc-helpers>

// <vc-spec>
fn flatten(mat: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        mat.len() > 0,
        forall|i: int| 0 <= i < mat.len() ==> mat[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat.len() ==> mat[i].len() == mat[j].len(),
    ensures 
        result.len() == mat.len() * mat[0].len(),
        forall|r: int, c: int| 
            0 <= r < mat.len() && 0 <= c < mat[0].len() ==>
            result[r * mat[0].len() + c] == mat[r][c]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type annotations and bounds checking */
    let rows = mat.len();
    let cols = mat[0].len();
    
    let mut result: Vec<f32> = Vec::new();
    
    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r <= rows,
            rows > 0,
            cols > 0,
            result.len() == r * cols,
            forall|row: int, col: int|
                0 <= row < r && 0 <= col < cols ==>
                0 <= row * cols + col < result.len() &&
                result@[row * cols + col] == mat@[row]@[col]
        decreases rows - r
    {
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= r < rows,
                0 <= c <= cols,
                rows > 0,
                cols > 0,
                result.len() == r * cols + c,
                forall|row: int, col: int|
                    0 <= row < r && 0 <= col < cols ==>
                    0 <= row * cols + col < result.len() &&
                    result@[row * cols + col] == mat@[row]@[col],
                forall|col_idx: int|
                    0 <= col_idx < c ==>
                    0 <= r * cols + col_idx < result.len() &&
                    result@[r * cols + col_idx] == mat@[r as int]@[col_idx]
            decreases cols - c
        {
            proof {
                index_bounds_lemma(r as int, c as int, rows as int, cols as int);
                assert(0 <= r < rows);
                assert(0 <= c < cols);
                assert(0 <= r < mat.len());
                assert(0 <= c < mat@[r as int].len());
            }
            result.push(mat[r][c]);
            c += 1;
        }
        r += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
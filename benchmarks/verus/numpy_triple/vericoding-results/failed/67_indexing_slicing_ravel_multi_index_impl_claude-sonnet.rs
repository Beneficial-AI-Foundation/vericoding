// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed indexing to use int instead of usize */
fn bounds_check_lemma(row_indices: &Vec<u8>, col_indices: &Vec<u8>, rows: u8, cols: u8, i: int)
    requires
        0 <= i < row_indices.len(),
        row_indices.len() == col_indices.len(),
        forall|j: int| 0 <= j < row_indices.len() ==> (row_indices[j] as nat) < (rows as nat),
        forall|j: int| 0 <= j < col_indices.len() ==> (col_indices[j] as nat) < (cols as nat),
    ensures
        i < col_indices.len(),
        (row_indices[i] as nat) * (cols as nat) + (col_indices[i] as nat) < 256,
{}
// </vc-helpers>

// <vc-spec>
fn ravel_multi_index(row_indices: &Vec<u8>, col_indices: &Vec<u8>, rows: u8, cols: u8) -> (result: Vec<u8>)
    requires 
        row_indices.len() == col_indices.len(),
        forall|i: int| 0 <= i < row_indices.len() ==> (row_indices[i] as nat) < (rows as nat),
        forall|i: int| 0 <= i < col_indices.len() ==> (col_indices[i] as nat) < (cols as nat),
    ensures 
        result.len() == row_indices.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] as nat) == (row_indices[i] as nat) * (cols as nat) + (col_indices[i] as nat) && 
            (result[i] as nat) < (rows as nat) * (cols as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by converting int to usize for indexing */
    let mut result: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < row_indices.len()
        invariant
            i <= row_indices.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==>
                j < row_indices.len() && j < col_indices.len() &&
                (result[j] as nat) == (row_indices[j] as nat) * (cols as nat) + (col_indices[j] as nat) &&
                (result[j] as nat) < (rows as nat) * (cols as nat),
        decreases row_indices.len() - i
    {
        proof {
            bounds_check_lemma(row_indices, col_indices, rows, cols, i as int);
            assert(i < col_indices.len());
            assert((row_indices[i as int] as nat) * (cols as nat) + (col_indices[i as int] as nat) < 256);
        }
        let flat_index = row_indices[i] * cols + col_indices[i];
        result.push(flat_index);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
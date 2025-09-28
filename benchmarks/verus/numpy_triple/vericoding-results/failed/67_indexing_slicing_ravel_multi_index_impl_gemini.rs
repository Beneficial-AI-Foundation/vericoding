// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let mut result = Vec::<u8>::new();
    let mut i: usize = 0;
    while i < row_indices.len()
        invariant
            0 <= i <= row_indices.len(),
            col_indices.len() == row_indices.len(),
            result.len() == i,
            forall|j: int| 0 <= j < row_indices.len() ==> (row_indices[j] as nat) < (rows as nat),
            forall|j: int| 0 <= j < col_indices.len() ==> (col_indices[j] as nat) < (cols as nat),
            forall|k: int| 0 <= k < i ==> 
                (result[k] as nat) == (row_indices[k] as nat) * (cols as nat) + (col_indices[k] as nat),
            forall|k: int| 0 <= k < i ==> 
                (result[k] as nat) < (rows as nat) * (cols as nat),
        decreases row_indices.len() - i
    {
        let row_idx = row_indices[i];
        let col_idx = col_indices[i];

        let val = (row_idx as u64) * (cols as u64) + (col_idx as u64);

        result.push(val as u8);
        
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
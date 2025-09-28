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
    /* code modified by LLM (iteration 5): Fixed overflow check to use regular arithmetic instead of nat */
    // Need to ensure the result fits in u8
    // Check if rows * cols > 256 would overflow u8
    if rows > 0 && cols > 0 && (256 / rows < cols || rows * cols > 255) {
        // Cannot proceed - results would overflow u8
        return Vec::new();
    }
    
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    
    proof {
        // Establish the invariant that rows * cols <= 256
        if rows == 0 || cols == 0 {
            assert((rows as nat) * (cols as nat) == 0);
        } else {
            assert(rows * cols <= 255);
            assert((rows as nat) * (cols as nat) <= 255);
        }
        assert((rows as nat) * (cols as nat) <= 256);
    }
    
    while i < row_indices.len()
        invariant
            i <= row_indices.len(),
            result.len() == i,
            row_indices.len() == col_indices.len(),
            (rows as nat) * (cols as nat) <= 256,
            forall|j: int| 0 <= j < i ==> 
                (result[j] as nat) == (row_indices[j] as nat) * (cols as nat) + (col_indices[j] as nat) &&
                (result[j] as nat) < (rows as nat) * (cols as nat),
            forall|j: int| 0 <= j < row_indices.len() ==> (row_indices[j] as nat) < (rows as nat),
            forall|j: int| 0 <= j < col_indices.len() ==> (col_indices[j] as nat) < (cols as nat),
        decreases row_indices.len() - i
    {
        let row_idx = row_indices[i];
        let col_idx = col_indices[i];
        
        proof {
            assert((row_idx as nat) < (rows as nat));
            assert((col_idx as nat) < (cols as nat));
            assert((row_idx as nat) * (cols as nat) < (rows as nat) * (cols as nat));
            assert((row_idx as nat) * (cols as nat) + (col_idx as nat) < (rows as nat) * (cols as nat));
            assert((rows as nat) * (cols as nat) <= 256);
            assert((row_idx as nat) * (cols as nat) + (col_idx as nat) < 256);
        }
        
        let flat_idx: u8 = row_idx * cols + col_idx;
        
        proof {
            assert((flat_idx as nat) == (row_idx as nat) * (cols as nat) + (col_idx as nat));
            assert((flat_idx as nat) < (rows as nat) * (cols as nat));
        }
        
        result.push(flat_idx);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add proper preconditions to prevent overflow */
fn ravel_multi_index_helper(row: u8, col: u8, cols: u8) -> (result: u8)
    requires
        (row as nat) * (cols as nat) + (col as nat) < 256,
        (cols as nat) > 0,
    ensures
        (result as nat) == (row as nat) * (cols as nat) + (col as nat),
{
    let res_u32: u32 = (row as u32) * (cols as u32) + (col as u32);
    assert(res_u32 < 256);
    res_u32 as u8
}
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
    /* code modified by LLM (iteration 5): Add proper bounds checking and proof for vector access */
    let mut result: Vec<u8> = Vec::new();
    let n = row_indices.len();
    
    proof {
        assert(row_indices@.len() == col_indices@.len());
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result[j] as nat) == (row_indices[j] as nat) * (cols as nat) + (col_indices[j] as nat),
            forall|j: int| 0 <= j < i ==> (result[j] as nat) < (rows as nat) * (cols as nat),
        decreases n - i,
    {
        proof {
            assert(i < row_indices@.len());
            assert(i < col_indices@.len());
        }
        let row_val = row_indices[i];
        let col_val = col_indices[i];
        
        proof {
            assert((row_val as nat) < (rows as nat));
            assert((col_val as nat) < (cols as nat));
            assert((row_val as nat) * (cols as nat) + (col_val as nat) < (rows as nat) * (cols as nat));
            assert((rows as nat) * (cols as nat) <= 256 * 256);
        }
        
        let index = ravel_multi_index_helper(row_val, col_val, cols);
        result.push(index);
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
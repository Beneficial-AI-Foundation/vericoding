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
    /* code modified by LLM (iteration 5): Fixed indexing preconditions by using separate exec and spec indexing to satisfy Verus invariants */
    let mut result = Vec::<u8>::new();
    let mut i = 0nat;
    while i < row_indices.len() as nat
        invariant
            i <= row_indices.len() as nat,
            result.len() == i,
            forall|j: nat| 0 <= j < i ==> 
                (result[j] as nat) == (row_indices@[j] as nat) * (cols as nat) + (col_indices@[j] as nat),
        decreases (row_indices.len() as nat - i)
    {
        proof {
            assert(i < row_indices.len() as nat);
            assert(i < col_indices.len() as nat);  // equal length
            assert((row_indices@[i] as nat) * (cols as nat) + (col_indices@[i] as nat) < (rows as nat) * (cols as nat));
        }
        let row_usize = row_indices[i as usize];
        let col_usize = col_indices[i as usize];
        let cols_usize = cols as usize;
        let idx_usize = row_usize * cols_usize + col_usize;
        #[verifier::truncate]
        let idx_u8 = idx_usize as u8;
        result.push(idx_u8);
        i = i + 1nat;
    }
    result
}
// </vc-code>

}
fn main() {}
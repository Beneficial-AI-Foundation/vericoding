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
/* code modified by LLM (iteration 4): Removed use of `capacity()` as suggested by compilation error */
{
    let len = row_indices.len();
    let mut result_vec: Vec<u8> = Vec::new();
    // result_vec.reserve(len); // Not needed without capacity() checks
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i && i <= len,
            result_vec.len() == i,
            // result_vec.capacity() >= len, // Removed due to compilation error
            forall|j: int| 0 <= j < i ==> {
                let row_idx = row_indices@[j] as nat;
                let col_idx = col_indices@[j] as nat;
                let cols_nat = cols as nat;
                (result_vec@[j] as nat) == (row_idx * cols_nat + col_idx) &&
                (result_vec@[j] as nat) < (rows as nat) * cols_nat
            },
    {
        let row_idx_val = row_indices[i];
        let col_idx_val = col_indices[i];
        let cols_val = cols;

        let calculated_val: nat;
        proof {
            let row_idx = row_idx_val as nat;
            let col_idx = col_idx_val as nat;
            let cols_nat = cols_val as nat;
            calculated_val = row_idx * cols_nat + col_idx;
            assert(calculated_val < (rows as nat) * cols_nat)
                by_nonlinear_arithmetic
                requires
                    row_idx < (rows as nat),
                    col_idx < (cols as nat),
                ensures
                    calculated_val < (rows as nat) * (cols as nat);
        }

        result_vec.push(calculated_val as u8);

        i = i + 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}
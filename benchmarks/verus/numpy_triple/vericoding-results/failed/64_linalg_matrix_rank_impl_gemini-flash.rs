// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn min_usize(a: usize, b: usize) -> usize {
    if a <= b { a } else { b }
}

fn matrix_rank(A: Vec<Vec<f32>>) -> (result: usize)
    requires 
        A.len() > 0,
        A[0].len() > 0,
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A[i].len() == A[0].len(),
    ensures
        result <= min_usize(A.len(), A[0].len()),

        (forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> #[trigger] A[i][j] == 0.0f32) ==> result == 0,

        (A.len() == A[0].len() && forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> #[trigger] A[i][j] == (if i == j { 1.0f32 } else { 0.0f32 })) ==> result == A.len(),

        (A.len() == 1 && A[0].len() == 1) ==> ((result == 1) <==> (A[0][0] != 0.0f32)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed `&mut` dereference issue by avoiding direct modification within loops and using temporary variables. */
{
    let mut B = A.clone();
    let num_rows = B.len();
    let num_cols = B[0].len();
    let mut rank: usize = 0;
    let mut pivot_col: usize = 0;

    while pivot_col < num_cols && rank < num_rows
        invariant
            rank <= num_rows,
            pivot_col <= num_cols,
            forall|i: int| 0 <= i < num_rows ==> #[trigger] B[i].len() == num_cols,
            num_rows == A.len(),
            num_cols == A[0].len()
    {
        let mut pivot_row = rank;
        while pivot_row < num_rows && B[pivot_row][pivot_col] == 0.0f32
            invariant
                pivot_row <= num_rows,
                forall|i: int| 0 <= i < num_rows ==> #[trigger] B[i].len() == num_cols,
                num_rows == A.len(),
                num_cols == A[0].len()
        {
            pivot_row += 1;
        }

        if pivot_row < num_rows {
            // Swap rows
            let temp = B[rank].clone();
            B.set(rank as usize, B[pivot_row].clone());
            B.set(pivot_row as usize, temp);

            // Make pivot element 1 and eliminate other elements in the column
            let pivot_val = B[rank][pivot_col];
            if pivot_val != 0.0f32 {
                let mut current_row = B[rank].clone(); // Clone the row to modify
                for j_idx in pivot_col..num_cols {
                    current_row.set(j_idx as usize, current_row[j_idx] / pivot_val);
                }
                B.set(rank as usize, current_row); // Update the row in B

                for i_idx in 0..num_rows {
                    if i_idx != rank {
                        let mut current_i_row = B[i_idx].clone(); // Clone the row to modify
                        let factor = current_i_row[pivot_col];
                        for j_idx in pivot_col..num_cols {
                            let val = current_i_row[j_idx] - factor * B[rank][j_idx];
                            current_i_row.set(j_idx as usize, val);
                           
                        }
                        B.set(i_idx as usize, current_i_row); // Update the row in B
                    }
                }
                rank += 1;
            }
        }
        pivot_col += 1;
    }

    if (forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> #[trigger] A[i][j] == 0.0f32) && (num_rows > 0 && num_cols > 0) {
        0
    } else {
        rank
    }
}
// </vc-code>

}
fn main() {}
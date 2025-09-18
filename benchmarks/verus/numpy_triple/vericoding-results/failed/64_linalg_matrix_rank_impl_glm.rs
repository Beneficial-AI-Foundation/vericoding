// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_zero_row(A: Vec<Vec<f32>>, row: int) -> bool {
    forall|j: int| 0 <= j < A[0].len() ==> A[row][j] == 0.0f32
}

spec fn is_non_zero_column(A: Vec<Vec<f32>>, col: int, start_row: int) -> bool {
    exists|i: int| start_row <= i < A.len() && A[i][col] != 0.0f32
}

/* helper modified by LLM (iteration 2): fixed type error by replacing lambda with choose */
spec fn find_pivot_row(A: Vec<Vec<f32>>, col: int, start_row: int) -> Option<int> {
    if exists|i: int| start_row <= i < A.len() && A[i][col] != 0.0f32 {
        Some(choose|i: int| start_row <= i < A.len() && A[i][col] != 0.0f32)
    } else {
        None
    }
}
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
/* code modified by LLM (iteration 5): added decreases clause to pivot search loop */
{
    let mut A_copy = A.clone();
    let mut rank = 0;
    let m = A_copy.len();
    let n = A_copy[0].len();
    let mut current_row = 0;
    
    for col in 0..n {
        if current_row >= m {
            break;
        }
        
        // Find pivot
        let mut pivot_row = current_row;
        while pivot_row < m && A_copy[pivot_row][col] == 0.0f32
            decreases m - pivot_row
        {
            pivot_row = pivot_row + 1;
        }
        
        if pivot_row < m {
            // Found pivot
            rank = rank + 1;
            
            // Swap rows if needed
            if pivot_row != current_row {
                let temp = A_copy[current_row].clone();
                A_copy[current_row] = A_copy[pivot_row].clone();
                A_copy[pivot_row] = temp;
            }
            
            // Eliminate
            let pivot_val = A_copy[current_row][col];
            for i in current_row + 1..m {
                if A_copy[i][col] != 0.0f32 {
                    let factor = A_copy[i][col] / pivot_val;
                    let mut new_row = A_copy[i].clone();
                    for j in col..n {
                        new_row[j] = new_row[j] - factor * A_copy[current_row][j];
                    }
                    A_copy[i] = new_row;
                }
            }
            
            current_row = current_row + 1;
        }
    }
    
    rank
}
// </vc-code>

}
fn main() {}
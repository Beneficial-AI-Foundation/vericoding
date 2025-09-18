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
{
    /* code modified by LLM (iteration 5): Added decreases clause to main loop */
    let m = A.len();
    let n = A[0].len();
    let mut work_matrix: Vec<Vec<f32>> = Vec::new();
    let mut i = 0;
    while i < m
        invariant
            i <= m,
            work_matrix.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] work_matrix[k].len() == n,
        decreases m - i,
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j = 0;
        while j < n
            invariant
                j <= n,
                row.len() == j,
            decreases n - j,
        {
            row.push(A[i][j]);
            j = j + 1;
        }
        work_matrix.push(row);
        i = i + 1;
    }
    
    let mut rank: usize = 0;
    let mut col = 0;
    let mut row = 0;
    
    while row < m && col < n
        invariant
            row <= m,
            col <= n,
            rank <= row,
            rank <= col,
            work_matrix.len() == m,
            forall|k: int| 0 <= k < m ==> #[trigger] work_matrix[k].len() == n,
        decreases m + n - row - col,
    {
        let mut pivot_row = row;
        let mut max_val = if work_matrix[row][col] < 0.0f32 { -work_matrix[row][col] } else { work_matrix[row][col] };
        let mut i = row + 1;
        
        while i < m
            invariant
                row < i,
                i <= m,
                pivot_row >= row,
                pivot_row < m,
            decreases m - i,
        {
            let abs_val = if work_matrix[i][col] < 0.0f32 { -work_matrix[i][col] } else { work_matrix[i][col] };
            if abs_val > max_val {
                max_val = abs_val;
                pivot_row = i;
            }
            i = i + 1;
        }
        
        if work_matrix[pivot_row][col] == 0.0f32 {
            col = col + 1;
        } else {
            if pivot_row != row {
                let temp = work_matrix[row].clone();
                work_matrix.set(row, work_matrix[pivot_row].clone());
                work_matrix.set(pivot_row, temp);
            }
            
            let mut i = row + 1;
            while i < m
                invariant
                    row < i,
                    i <= m,
                    work_matrix.len() == m,
                    forall|k: int| 0 <= k < m ==> #[trigger] work_matrix[k].len() == n,
                decreases m - i,
            {
                let factor = work_matrix[i][col] / work_matrix[row][col];
                let mut new_row: Vec<f32> = Vec::new();
                let mut j = 0;
                while j < n
                    invariant
                        j <= n,
                        new_row.len() == j,
                    decreases n - j,
                {
                    if j < col {
                        new_row.push(work_matrix[i][j]);
                    } else {
                        let new_val = work_matrix[i][j] - factor * work_matrix[row][j];
                        new_row.push(new_val);
                    }
                    j = j + 1;
                }
                work_matrix.set(i, new_row);
                i = i + 1;
            }
            
            rank = rank + 1;
            row = row + 1;
            col = col + 1;
        }
    }
    
    rank
}
// </vc-code>

}
fn main() {}
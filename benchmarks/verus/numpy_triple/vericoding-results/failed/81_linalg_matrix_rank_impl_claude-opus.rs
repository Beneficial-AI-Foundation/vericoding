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
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A[i as int].len() == A[0].len(),
    ensures
        result <= min_usize(A.len(), A[0].len()),

        (forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> #[trigger] A[i as int][j as int] == 0.0f32) ==> result == 0,

        (A.len() == A[0].len() && forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> #[trigger] A[i as int][j as int] == (if i == j { 1.0f32 } else { 0.0f32 })) ==> result == A.len(),

        (A.len() == 1 && A[0].len() == 1) ==> ((result == 1) <==> (A[0][0] != 0.0f32)),
// </vc-spec>
// <vc-code>
{
    let m = A.len();
    let n = A[0].len();
    let mut mat = A;
    let mut rank: usize = 0;
    
    let mut col: usize = 0;
    while col < n && rank < m
        invariant
            mat.len() == m,
            n > 0,
            m > 0,
            mat[0].len() == n,
            forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i as int].len() == n,
            col <= n,
            rank <= m,
            rank <= col,
            rank <= min_usize(m, n),
    {
        let mut pivot_row: usize = rank;
        let mut found_pivot = false;
        
        let mut row: usize = rank;
        while row < m
            invariant
                mat.len() == m,
                mat[0].len() == n,
                forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i as int].len() == n,
                rank <= row,
                row <= m,
                rank < m,
                col < n,
                pivot_row >= rank,
                pivot_row < m,
        {
            if mat[row][col] != 0.0f32 {
                pivot_row = row;
                found_pivot = true;
                break;
            }
            row = row + 1;
        }
        
        if !found_pivot {
            col = col + 1;
            continue;
        }
        
        if pivot_row != rank {
            let temp = mat[rank];
            mat.set(rank, mat[pivot_row]);
            mat.set(pivot_row, temp);
        }
        
        let pivot = mat[rank][col];
        
        let mut j: usize = 0;
        while j < n
            invariant
                mat.len() == m,
                mat[0].len() == n,
                forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i as int].len() == n,
                j <= n,
                rank < m,
                col < n,
        {
            mat[rank].set(j, mat[rank][j] / pivot);
            j = j + 1;
        }
        
        let mut i: usize = 0;
        while i < m
            invariant
                mat.len() == m,
                mat[0].len() == n,
                forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i as int].len() == n,
                i <= m,
                rank < m,
                col < n,
        {
            if i != rank && mat[i][col] != 0.0f32 {
                let factor = mat[i][col];
                let mut j2: usize = 0;
                while j2 < n
                    invariant
                        mat.len() == m,
                        mat[0].len() == n,
                        forall|k: int| 0 <= k < mat.len() ==> #[trigger] mat[k as int].len() == n,
                        j2 <= n,
                        i < m,
                        rank < m,
                {
                    mat[i].set(j2, mat[i][j2] - factor * mat[rank][j2]);
                    j2 = j2 + 1;
                }
            }
            i = i + 1;
        }
        
        rank = rank + 1;
        col = col + 1;
    }
    
    rank
}
// </vc-code>

}
fn main() {}
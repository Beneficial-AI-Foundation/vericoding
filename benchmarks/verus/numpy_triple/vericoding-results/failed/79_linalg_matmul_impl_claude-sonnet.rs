// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add helper functions for safe matrix access and bounds checking */
fn matrix_rows(m: &Vec<Vec<i8>>) -> (result: usize)
    requires m.len() > 0,
    ensures result == m.len(),
{
    m.len()
}

fn matrix_cols(m: &Vec<Vec<i8>>) -> (result: usize)
    requires m.len() > 0,
    ensures result == m@[0].len(),
{
    m[0].len()
}
// </vc-helpers>

// <vc-spec>
fn matmul(A: Vec<Vec<i8>>, B: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
    requires
        A.len() > 0,
        B.len() > 0,
        A@[0].len() == B.len(),
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A@[i].len() == A@[0].len(),
        forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == B@[0].len(),
    ensures
        result.len() == A.len(),
        result.len() > 0 ==> result@[0].len() == B@[0].len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i].len() == B@[0].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Add decreases clauses to all while loops */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let a_rows = A.len();
    let b_cols = B[0].len();
    let common_dim = A[0].len();
    
    let mut i = 0;
    while i < a_rows
        invariant
            i <= a_rows,
            a_rows == A.len(),
            b_cols == B@[0].len(),
            common_dim == A@[0].len(),
            common_dim == B.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == B@[0].len(),
        decreases a_rows - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j = 0;
        
        while j < b_cols
            invariant
                j <= b_cols,
                b_cols == B@[0].len(),
                common_dim == A@[0].len(),
                common_dim == B.len(),
                i < A.len(),
                row.len() == j,
            decreases b_cols - j
        {
            let mut sum: i8 = 0;
            let mut k = 0;
            
            while k < common_dim
                invariant
                    k <= common_dim,
                    common_dim == A@[0].len(),
                    common_dim == B.len(),
                    i < A.len(),
                    j < B@[0].len(),
                decreases common_dim - k
            {
                sum = sum + A[i][k] * B[k][j];
                k = k + 1;
            }
            
            row.push(sum);
            j = j + 1;
        }
        
        result.push(row);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
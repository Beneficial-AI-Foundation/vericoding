// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added trigger annotations for matrix indexing */
spec fn valid_indices(n: usize, i: usize, j: usize) -> bool { i < n && j < n }

spec fn is_lower_triangular(i: usize, j: usize) -> bool { i >= j }

spec fn matrix_index(i: usize, j: usize, n: usize) -> int { (i * n + j) as int }
// </vc-helpers>

// <vc-spec>
fn tril(matrix: Vec<f32>, n: usize) -> (result: Vec<f32>)
    requires 
        n > 0,
        matrix.len() == n * n,
    ensures
        result.len() == matrix.len(),
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == matrix[i * n + j] <==
            i < n && j < n && i >= j,
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == 0.0f32 <==
            i < n && j < n && i < j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed forall quantifier syntax */
    let mut result = Vec::with_capacity(matrix.len());
    let mut idx = 0;
    
    while idx < matrix.len()
        invariant
            n > 0,
            matrix.len() == n * n,
            idx <= matrix.len(),
            result.len() == idx,
            forall|k: usize| k < idx ==> {
                let i = k / n;
                let j = k % n;
                (i < n && j < n && i >= j ==> result[k as int] == matrix[k as int]) &&
                (i < n && j < n && i < j ==> result[k as int] == 0.0f32)
            }
        decreases matrix.len() - idx
    {
        let i = idx / n;
        let j = idx % n;
        
        if i >= j {
            result.push(matrix[idx]);
        } else {
            result.push(0.0f32);
        }
        
        idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
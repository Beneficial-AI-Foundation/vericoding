// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn diag(matrix: Vec<f32>, n: usize) -> (result: Vec<f32>)
    requires 
        matrix.len() == n * n,
        n > 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n as int ==> result@[i] == matrix@[i * n as int + i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant syntax by using let-in expression */
    let n_int = n as int;
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < n_int
        invariant
            0 <= i <= n_int,
            result.len() == i as usize,
            forall|j: int| 0 <= j < i ==> 
                let idx_j = j * n_int + j in
                0 <= idx_j < n_int * n_int && result@[j] == matrix@[idx_j],
        decreases n_int - i
    {
        let idx = i * n_int + i;
        proof {
            // Since i < n_int, we have i <= n_int - 1.
            // Then: idx = i * (n_int + 1) <= (n_int-1)*(n_int+1) = n_int*n_int - 1 < n_int*n_int.
            // Also, idx is nonnegative.
            assert(0 <= idx && idx < n_int * n_int);
        }
        let idx_usize = idx as usize;
        result.push(matrix[idx_usize]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
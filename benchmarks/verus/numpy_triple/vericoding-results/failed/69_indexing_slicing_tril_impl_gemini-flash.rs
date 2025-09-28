// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn tril(matrix: Vec<f32>, n: usize) -> (result: Vec<f32>)
    requires 
        n > 0,
        matrix.len() == n * n,
    ensures
        result.len() == matrix.len(),
        forall|i: usize, j: usize| #[trigger] result@[i * n + j] == matrix@[i * n + j] <==
            i < n && j < n && i >= j,
        forall|i: usize, j: usize| #[trigger] result@[i * n + j] == 0.0f32 <==
            i < n && j < n && i < j,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The error was a missing return type in the forall closure in the invariant. This cannot be fixed by adding curly braces. Instead, the `is (... )` must be removed and the assertion must happen inside the `==>` clause. */
{
    let mut result = Vec::new();
    result.reserve(n * n);

    let mut row_idx: usize = 0;
    while row_idx < n
        invariant
            0 <= row_idx,
            row_idx <= n,
            result.len() == row_idx * n,
            forall|i: usize, j: usize| #[trigger] (i * n + j) => { (0 <= i && i < row_idx && 0 <= j && j < n) ==> {
                (i >= j && result@[i * n + j] == matrix@[i * n + j]) ||
                (i < j && result@[i * n + j] == 0.0f32)
            }},
        decreases n - row_idx
    {
        let mut col_idx: usize = 0;
        while col_idx < n
            invariant
                0 <= row_idx,
                row_idx < n,
                0 <= col_idx,
                col_idx <= n,
                result.len() == row_idx * n + col_idx,
                forall|i: usize, j: usize| #[trigger] (i * n + j) => { (0 <= i && i < row_idx && 0 <= j && j < n) ==> {
                    (i >= j && result@[i * n + j] == matrix@[i * n + j]) ||
                    (i < j && result@[i * n + j] == 0.0f32)
                }},
                forall|k: usize| #[trigger] (row_idx * n + k) => { (0 <= k && k < col_idx) ==> {
                    (row_idx >= k && result@[row_idx * n + k] == matrix@[row_idx * n + k]) ||
                    (row_idx < k && result@[row_idx * n + k] == 0.0f32)
                }},
            decreases n - col_idx
        {
            if row_idx >= col_idx {
                result.push(matrix[row_idx * n + col_idx]);
            } else {
                result.push(0.0f32);
            }
            col_idx = col_idx + 1;
        }
        row_idx = row_idx + 1;
    }

    result
}
// </vc-code>

}
fn main() {}
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
{
    /* code modified by LLM (iteration 2): Added decreases clauses to both loops */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i * n,
            forall|row: usize, col: usize| row < i && col < n ==> #[trigger] result@[row * n + col] == if row >= col { matrix@[row * n + col] } else { 0.0f32 },
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                result.len() == i * n + j,
                forall|row: usize, col: usize| row < i && col < n ==> #[trigger] result@[row * n + col] == if row >= col { matrix@[row * n + col] } else { 0.0f32 },
                forall|col: usize| col < j ==> #[trigger] result@[i * n + col] == if i >= col { matrix@[i * n + col] } else { 0.0f32 },
            decreases n - j
        {
            if i >= j {
                result.push(matrix[i * n + j]);
            } else {
                result.push(0.0f32);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
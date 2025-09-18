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
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == matrix[i * n + j] <==
            i < n && j < n && i >= j,
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == 0.0f32 <==
            i < n && j < n && i < j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed bounds checking for matrix access */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i * n,
            matrix.len() == n * n,
            n > 0,
            forall|row: usize, col: usize| row < i && col < n && row * n + col < result.len() ==> #[trigger] result[row * n + col] == if row >= col { matrix[row * n + col] } else { 0.0f32 },
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                i < n,
                result.len() == i * n + j,
                matrix.len() == n * n,
                n > 0,
                forall|row: usize, col: usize| row < i && col < n && row * n + col < result.len() ==> #[trigger] result[row * n + col] == if row >= col { matrix[row * n + col] } else { 0.0f32 },
                forall|col: usize| col < j && i * n + col < result.len() ==> #[trigger] result[i * n + col] == if i >= col { matrix[i * n + col] } else { 0.0f32 },
            decreases n - j
        {
            assert(i * n + j == result.len());
            assert(i < n && j < n);
            assert(matrix.len() == n * n);
            assert(i * n + j < n * n);
            if i >= j {
                result.push(matrix[i * n + j]);
            } else {
                result.push(0.0f32);
            }
            assert(result.len() == i * n + j + 1);
            j = j + 1;
        }
        i = i + 1;
    }
    assert(result.len() == n * n);
    assert(result.len() == matrix.len());
    result
}
// </vc-code>

}
fn main() {}
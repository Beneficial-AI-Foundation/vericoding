// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused helper */
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
/* code modified by LLM (iteration 5): Fixed loop invariants after review */
{
    let mut result: Vec<f32> = Vec::new();
    result.reserve(n * n);

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i * n,
            forall|row: usize, col: usize| #![trigger result[row*n + col]]
                row < i && col < n ==> (
                    (row >= col ==> result[row * n + col] == matrix[row * n + col]) &&
                    (row < col ==> result[row * n + col] == 0.0f32)
                ),
        decreases n - i,

    {
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                result.len() == i * n + j,
                0 <= i && i < n && 0 <= j && j <= n,
                forall|idx: usize| #![trigger result[idx]]
                    idx < i * n ==> (
                        0 <= idx / n && idx / n < i && 0 <= idx % n && idx % n < n
                        ==>
                        (
                            idx / n >= idx % n ==> result[idx] == matrix[idx]
                        ) && (
                            idx / n < idx % n ==> result[idx] == 0.0f32
                        )
                    ),
                forall|col: usize| #![trigger result[i*n + col]]
                    col < j && 0 <= i && i < n && 0 <= col && col < n
                    ==>
                    (
                        (i >= col ==> result[i * n + col] == matrix[i * n + col]) &&
                        (i < col ==> result[i * n + col] == 0.0f32)
                    ),

                result.len() == i * n + j,
                matrix.len() == n * n,
                n > 0,
            decreases n - j,

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
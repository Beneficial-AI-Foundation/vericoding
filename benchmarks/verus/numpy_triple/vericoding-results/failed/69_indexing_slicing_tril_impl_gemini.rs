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
    /* code modified by LLM (iteration 4): Added #[trigger] annotations to forall quantifiers in loop invariants to guide the verifier. */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n > 0,
            matrix.len() == n * n,
            result.len() == i * n,
            forall|r: usize, c: usize| 
                r < i && c < n && r >= c ==> #[trigger] result@[r * n + c] == matrix@[r * n + c],
            forall|r: usize, c: usize| 
                r < i && c < n && r < c ==> #[trigger] result@[r * n + c] == 0.0f32,
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                i < n,
                0 <= j <= n,
                n > 0,
                matrix.len() == n * n,
                result.len() == i * n + j,
                forall|r: usize, c: usize| 
                    r < i && c < n && r >= c ==> #[trigger] result@[r * n + c] == matrix@[r * n + c],
                forall|r: usize, c: usize| 
                    r < i && c < n && r < c ==> #[trigger] result@[r * n + c] == 0.0f32,
                forall|c: usize| 
                    c < j && i >= c ==> #[trigger] result@[i * n + c] == matrix@[i * n + c],
                forall|c: usize| 
                    c < j && i < c ==> #[trigger] result@[i * n + c] == 0.0f32,
            decreases n - j
        {
            let index = i * n + j;
            if i >= j {
                result.push(matrix[index]);
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
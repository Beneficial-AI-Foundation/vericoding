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
    /* code modified by LLM (iteration 3): fixed type mismatch in invariant by casting k to int */
    let mut result = Vec::new();
    let mut index = 0;
    while index < n * n
        invariant
            index <= n * n,
            result.len() == index,
            forall|k: usize| k < index ==> {
                let i = k / n;
                let j = k % n;
                (i >= j ==> result@[k as int] == matrix@[k as int]) && (i < j ==> result@[k as int] == 0.0f32)
            }
        decreases n * n - index
    {
        let i = index / n;
        let j = index % n;
        if i >= j {
            result.push(matrix[index]);
        } else {
            result.push(0.0f32);
        }
        index += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
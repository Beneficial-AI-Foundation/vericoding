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
/* code modified by LLM (iteration 5): Fixed type casting from usize to int for indexing */
{
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            result.len() == i,
            0 <= i,
            i <= n,
            forall|j: int| 0 <= j < i as int ==> result@[j] == matrix@((j * n) as int + j)
    {
        result.push(matrix@(((i * n) + i) as int));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
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
    /* code modified by LLM (iteration 5): Changed loop index i to usize to fix compilation error with Verus types nat/int outside ghost code. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == matrix@[j * (n as int) + j],
            forall|j: int| 0 <= j < i as int ==> 0 <= j * (n as int) + j < (n as int) * (n as int),
        decreases n - i
    {
        let idx = i * n + i;
        result.push(matrix[idx]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
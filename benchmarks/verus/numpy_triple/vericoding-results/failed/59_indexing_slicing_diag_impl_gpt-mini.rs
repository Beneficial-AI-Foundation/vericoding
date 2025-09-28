// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute linear index of i-th diagonal element */
fn diag_index(i: usize, n: usize) -> (res: usize)
    requires
        i < n,
    ensures
        res == i * n + i,
{
    let res = i * n + i;
    res
}
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
    /* code modified by LLM (iteration 5): extract diagonal elements using diag_index helper with usize */
    let mut result: Vec<f32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            result.len() == k,
            forall|j: int| 0 <= j < k as int ==> result@[j] == matrix@[j * n as int + j],
        decreases n - k
    {
        let idx: usize = diag_index(k, n);
        let val: f32 = matrix[idx];
        result.push(val);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
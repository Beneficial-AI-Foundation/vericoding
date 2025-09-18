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
        forall|i: int| 0 <= i < n ==> result[i] == matrix[i * n + i],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<f32> = Vec::new();
    let mut i: int = 0;
    while i < n as int
        invariant
            0 <= i <= n as int,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == matrix[(j * n + j) as usize],
    {
        let idx = (i * n + i) as usize;
        result.push(matrix[idx]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
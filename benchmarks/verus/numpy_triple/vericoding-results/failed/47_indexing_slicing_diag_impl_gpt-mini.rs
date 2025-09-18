// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proof that diagonal index is within bounds */
proof fn diag_index_bound(j: int, n: int)
    requires 0 <= j && j < n && n > 0
    ensures (j * n + j) >= 0 && (j * n + j) < n * n
{
    proof {
        assert((j * n + j) >= 0);
        assert(j * n + j < n * n);
    }
}
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
    /* code modified by LLM (iteration 5): extract diagonal using usize loop var and maintain invariants */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n;
        invariant result.len() == i;
        invariant forall |j: int| 0 <= j && j < i as int ==> result[j as usize] == matrix[(j as usize) * n + (j as usize)];
        decreases n - i
    {
        let v: f32 = matrix[i * n + i];
        result.push(v);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
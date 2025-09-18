// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by removing invalid 'by(integer_ring)' prover hint */
proof fn lemma_diag_index_in_bounds(i: int, n: int)
    requires
        0 <= i < n,
        n > 0,
    ensures
        0 <= i * n + i,
        i * n + i < n * n,
{
    // Proof for 0 <= i * n + i
    assert(i * n >= 0) by(nonlinear_arith);
    assert(i * n + i >= 0);

    // Proof for i * n + i < n * n
    assert(i * n + i < n * n) by {
        assert(i <= n - 1);
        assert(n + 1 > 0);
        // Since i <= n-1 and n+1 > 0, we have i*(n+1) <= (n-1)*(n+1)
        assert(i * (n + 1) <= (n - 1) * (n + 1)) by(nonlinear_arith);
        // i*(n+1) = i*n + i, and (n-1)*(n+1) = n*n - 1
        assert(i * n + i <= n * n - 1) by(nonlinear_arith);
        assert(n * n - 1 < n * n);
    };
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
    /* code modified by LLM (iteration 5): no changes required */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n > 0,
            matrix.len() == n * n,
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == matrix@[j * (n as int) + j],
        decreases n - i
    {
        proof {
            lemma_diag_index_in_bounds(i as int, n as int);
        }
        let val = matrix[i * n + i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove flattened index i*n + j is within n*n by reasoning on integer casts */
fn linear_index_bound(n: usize, i: usize, j: usize)
    requires
        n > 0,
        i < n,
        j < n,
    ensures
        i * n + j < n * n,
{
    proof {
        let ii: int = i as int;
        let jj: int = j as int;
        let nn: int = n as int;
        // ii, jj in [0, nn)
        assert(0 <= ii && ii < nn);
        assert(0 <= jj && jj < nn);
        assert(nn > 0);
        // ii * nn + jj < nn * nn because ii <= nn-1 and jj <= nn-1
        assert(ii * nn + jj < nn * nn);
        // lift back to usize inequality
        assert(i * n + j < n * n);
    }
}
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
    /* code modified by LLM (iteration 5): set above-diagonal elements to 0 with strengthened invariants and index bounds */
    let mut result = matrix.clone();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall |ii: usize, jj: usize| #[trigger] result@[ii * n + jj] == if ii >= jj { matrix@[ii * n + jj] } else { 0.0f32 } <== ii < i && ii < n && jj < n,
        decreases n - i
    {
        assert(i < n);
        let mut j: usize = i + 1;
        while j < n
            invariant
                j <= n,
                forall |jj: usize| #[trigger] result@[i * n + jj] == if i >= jj { matrix@[i * n + jj] } else { 0.0f32 } <== jj < j && i < n && jj < n,
            decreases n - j
        {
            assert(i < n);
            assert(j < n);
            linear_index_bound(n, i, j);
            result.set(i * n + j, 0.0f32);
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
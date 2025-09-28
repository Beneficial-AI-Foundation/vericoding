// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove row-major index bound without subtraction */
proof fn helper_index_bound(n: usize, i: usize, j: usize)
    requires
        n > 0,
        i < n,
        j < n,
    ensures
        i * n + j < n * n,
{
    assert(j < n);
    // From j < n, adding i*n on both sides preserves <
    assert(i * n + j < i * n + n);
    // Algebraic identity
    assert(i * n + n == (i + 1) * n);
    // From i < n, we have i + 1 <= n
    assert(i + 1 <= n);
    // Monotonicity of multiplication by n (> 0)
    assert((i + 1) * n <= n * n);
    // Conclude the bound
    assert(i * n + j < n * n);
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
    /* code modified by LLM (iteration 5): implement tril via nested loops with proof of bounds */
    let len = matrix.len();
    let mut result_vec: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            len == matrix.len(),
            i <= n,
            result_vec.len() == i * n,
            forall|ii: usize, jj: usize|
                ii < i && jj < n ==> result_vec@[((ii * n) + jj) as int] ==
                    if ii >= jj { matrix@[((ii * n) + jj) as int] } else { 0.0f32 },
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                len == matrix.len(),
                i < n,
                j <= n,
                result_vec.len() == i * n + j,
                forall|ii: usize, jj: usize|
                    ii < i && jj < n ==> result_vec@[((ii * n) + jj) as int] ==
                        if ii >= jj { matrix@[((ii * n) + jj) as int] } else { 0.0f32 },
                forall|jj: usize|
                    jj < j ==> result_vec@[((i * n) + jj) as int] ==
                        if i >= jj { matrix@[((i * n) + jj) as int] } else { 0.0f32 },
            decreases n - j
        {
            let idx: usize = i * n + j;
            proof { helper_index_bound(n, i, j); }
            assert(idx < len);
            let val: f32 = if i >= j { matrix[idx] } else { 0.0f32 };
            result_vec.push(val);
            j += 1;
        }
        i += 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}
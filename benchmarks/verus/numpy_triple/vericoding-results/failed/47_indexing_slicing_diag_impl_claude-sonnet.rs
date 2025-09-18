// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed undefined mul_monotonic_left function */
spec fn matrix_index(i: int, n: int) -> int { i * n + i }

spec fn valid_matrix_access(i: int, n: int) -> bool {
    0 <= i < n && 0 <= matrix_index(i, n) < n * n
}

proof fn matrix_access_bounds(i: int, n: int)
    requires 0 <= i < n, n > 0
    ensures valid_matrix_access(i, n)
{
    assert(i * n >= 0);
    assert(i < n);
    assert(i * n < n * n) by {
        assert(i < n);
        assert(i * n <= (n - 1) * n) by {
            assert(i <= n - 1);
            assert(i * n <= (n - 1) * n);
        };
        assert((n - 1) * n < n * n) by {
            assert((n - 1) * n == n * n - n);
            assert(n > 0);
        };
    };
    assert(i * n + i < n * n) by {
        assert(i * n < n * n - n);
        assert(i < n);
        assert(i * n + i < n * n - n + n);
        assert(n * n - n + n == n * n);
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
    /* code modified by LLM (iteration 5): simplified proof approach */
    let mut result = Vec::new();
    let mut idx = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            result.len() == idx,
            forall|j: int| 0 <= j < idx ==> result[j] == matrix[j * n + j],
            matrix.len() == n * n,
            n > 0,
        decreases n - idx
    {
        let diag_idx = idx * n + idx;
        assert(diag_idx < matrix.len()) by {
            assert(idx < n);
            assert(idx * n + idx < n * n);
        };
        result.push(matrix[diag_idx]);
        idx += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
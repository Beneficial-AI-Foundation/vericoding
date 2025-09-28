// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix proof helper to correctly handle type conversions and simplify bounds checks */
proof fn matrix_index_in_bounds(i: int, n: int)
    requires
        0 <= i < n,
        n > 0,
    ensures
        i * n + i >= 0,
        i * n + i < n * n,
{
    assert(i * n + i >= 0) by {
        assert(i >= 0);
        assert(n > 0);
    };
    assert(i * n + i < n * n) by {
        assert(i < n);
        assert(i * n <= (n - 1) * n);
        assert(i * n + i <= (n - 1) * n + (n - 1));
        assert((n - 1) * n + (n - 1) == n * n - n + n - 1);
        assert(n * n - n + n - 1 == n * n - 1);
        assert(n * n - 1 < n * n);
    };
}

fn safe_mul_add(i: usize, n: usize, j: usize) -> (index: usize)
    requires
        i < n,
        n > 0,
    ensures
        index == i * n + j,
        index < n * n,
{
    let res = i * n + j;
    proof {
        matrix_index_in_bounds(i as int, n as int);
    }
    res
}

fn initialize_result(n: usize) -> (result: Vec<f32>)
    requires
        n > 0,
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < n as int ==> result@[i] == 0.0f32,
{
    let mut vec = Vec::new();
    vec.resize(n, 0.0f32);
    vec
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
/* code modified by LLM (iteration 5): fix compilation error with proper type casting and matrix index calculation */
{
    let mut result = initialize_result(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == n,
            forall|j: int| 0 <= j < n as int ==> (#[trigger] result@[j]) == 
                (if j < i as int { matrix@[j * (n as int) + j] } else { 0.0f32 }),
        decreases n - i,
    {
        proof {
            matrix_index_in_bounds(i as int, n as int);
            assert(i as int * n as int + i as int < n as int * n as int);
        }
        let index = safe_mul_add(i, n, i);
        result.set(i, matrix[index]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
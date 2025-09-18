// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix arithmetic bounds with proper nat/int conversions */
spec fn index_valid(matrix: Vec<f32>, n: usize, i: usize) -> bool {
    matrix.len() == n * n && i < n
}

proof fn matrix_diagonal_access_lemma(matrix: Vec<f32>, n: usize, i: usize)
    requires
        matrix.len() == n * n,
        i < n,
    ensures
        matrix[i * n + i] == matrix@[i * n + i]
{
}

proof fn diag_index_in_bounds_lemma(n: usize, i: usize)
    requires
        n > 0,
        i < n,
    ensures
        (i as nat) * (n as nat) + (i as nat) < (n as nat) * (n as nat)
{
    assert((i as int) < (n as int));
    assert((i as int) * (n as int) <= ((n as int) - 1) * (n as int));
    assert(((n as int) - 1) * (n as int) + ((n as int) - 1) == (n as int) * (n as int) - 1);
    assert((i as int) * (n as int) + (i as int) <= ((n as int) - 1) * (n as int) + ((n as int) - 1));
    assert((i as int) * (n as int) + (i as int) < (n as int) * (n as int));
}

proof fn diag_index_valid_lemma(n: usize, i: usize)
    requires
        n > 0,
        i < n,
    ensures
        i * n + i < n * n
{
    assert(i <= n - 1);
    assert(i * n <= (n - 1) * n);
    assert((n - 1) * n + (n - 1) == n * n - 1);
    assert(i * n + i <= (n - 1) * n + (n - 1));
    assert(i * n + i < n * n);
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
/* code modified by LLM (iteration 5): Add proper bounds checking and proof blocks */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == matrix[j * n + j],
        decreases n - i
    {
        proof {
            diag_index_valid_lemma(n, i);
            assert(i * n + i < n * n);
        }
        let diag_index = i * n + i;
        result.push(matrix[diag_index]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
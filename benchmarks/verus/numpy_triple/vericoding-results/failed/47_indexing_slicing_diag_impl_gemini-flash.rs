// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add helper to prove that i*n+i is within bounds up to n*n - 1 */
proof fn index_in_bounds(i: int, n: int)
    requires
        0 <= i < n,
        0 < n,
    ensures
        i * n + i < n * n,
{
    assert(i <= n - 1);
    assert(i * n + i <= (n - 1) * n + (n - 1));
    assert((n - 1) * n + (n - 1) == n * n - 1);
    assert(n * n - 1 < n * n);
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
/* code modified by LLM (iteration 5): Fixed type errors related to `usize` to `int` casting for indexing, and removed unnecessary explicit casts within the loop for `matrix.view()@` access */
{
    let mut i: usize = 0;
    let mut result: Vec<f32> = Vec::new();
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.view()@[j] == matrix.view()@[(j * n as int + j)],
        decreases (n - i)
    {
        let i_int: int = i as int;
        let n_int: int = n as int;
        index_in_bounds(i_int, n_int);
        assert(i_int * n_int + i_int < n_int * n_int);
        result.push(matrix@[i_int * n_int + i_int]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
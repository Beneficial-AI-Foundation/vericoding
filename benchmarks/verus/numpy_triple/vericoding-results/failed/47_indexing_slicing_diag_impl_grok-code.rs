// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by adding by{} to assert forall statements */
proof fn lemma_diag_bounds(n: int)
    requires
        n > 0,
    ensures
        forall|i: int| 0 <= i < n ==> 0 <= i * n + i < n * n
{
    let max_index = (n - 1) * n + (n - 1);
    assert forall |i: int| 0 <= i < n implies i * n + i <= max_index by {};
    assert(max_index == n * n - n + n - 1);
    assert(n * n - n + n - 1 == n * n - 1);
    assert forall |i: int| 0 <= i < n implies 0 <= i * n + i by {};
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
/* code modified by LLM (iteration 5): kept implementation and enhanced proof block for bounds assertion */
{
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < n as int
        invariant
            i <= n as int,
            result.len() == i as usize,
            forall|j: int| 0 <= j < i ==> result[j] == matrix@[(j * (n as int) + j)]
        decreases (n - i as usize)
    {
        proof {
            let index = i * (n as int) + i;
            assert(0 <= i);
            assert(i < n as int);
            assert(0 <= index);
            assert(index < n as int * n as int);
        }
        result.push(matrix@[i * (n as int) + i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
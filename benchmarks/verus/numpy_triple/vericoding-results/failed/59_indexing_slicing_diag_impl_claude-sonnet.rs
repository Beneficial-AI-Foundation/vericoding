// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added trigger annotations to fix quantifier inference */
fn matrix_index_valid(i: usize, n: usize) -> bool
{
    i < n && i * n + i < n * n
}

fn matrix_index_in_bounds(matrix: &Vec<f32>, i: usize, n: usize) -> (result: bool)
    requires
        matrix.len() == n * n,
        n > 0,
    ensures
        result == (i < n),
{
    i < n
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
{
    /* code modified by LLM (iteration 5): added trigger annotations to fix quantifier inference errors */
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            forall|j: int| #[trigger] (j * n as int + j) 0 <= j < i as int ==> 0 <= j * n as int + j < matrix.len() as int,
            forall|j: int| #[trigger] result@[j] 0 <= j < i as int ==> result@[j] == matrix@[j * n as int + j],
        decreases n - i
    {
        proof {
            assert(i < n);
            assert(i * n + i < n * n);
            assert(i * n + i < matrix.len());
        }
        result.push(matrix[i * n + i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof body using nonlinear_arith */
proof fn diag_index_in_bounds(j: int, n: int)
    requires
        0 <= j < n,
        n > 0,
    ensures
        0 <= j * n + j < n * n,
{
    assert(j * n + j >= 0) by(nonlinear_arith);
    assert(j * n + j < n * n) by(nonlinear_arith);
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
    /* code modified by LLM (iteration 5): added explicit proof block to maintain loop invariant */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            matrix.len() == n * n,
            n > 0,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                &&& 0 <= j * (n as int) + j < (n*n) as int
                &&& result@[j] == matrix@[j * (n as int) + j]
            },
        decreases (n - i)
    {
        let i_int = i as int;
        let n_int = n as int;

        diag_index_in_bounds(i_int, n_int);

        let index = i * n + i;
        let val = matrix[index];

        let old_result_view = result.view();
        result.push(val);

        proof {
            assert forall|j: int| 0 <= j < i_int + 1 implies
                (0 <= j * n_int + j < n_int * n_int) &&
                result@[j] == matrix@[j * n_int + j]
            by {
                if j < i_int {
                    assert(result@[j] == old_result_view@[j]);
                } else {
                    assert(j == i_int);
                }
            }
        }

        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}
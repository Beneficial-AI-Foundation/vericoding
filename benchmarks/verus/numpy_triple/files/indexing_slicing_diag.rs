use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
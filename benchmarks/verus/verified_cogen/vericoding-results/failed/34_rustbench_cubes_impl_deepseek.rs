// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix nat type usage in spec function */
spec fn cubes_helper(i: int) -> int
    ensures
        result == i * i * i
{
    i * i * i
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix result variable reference in ensures clause */
{
    let mut result_vec = Vec::new();
    let mut n: usize = 0;
    while n < len
        invariant
            result_vec.len() == n,
            forall|i: int| 0 <= i && i < n ==> result_vec[i] == cubes_helper(i)
        decreases len - n
    {
        let cube_val = cubes_helper(n as int) as i32;
        result_vec.push(cube_val);
        n = n + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed extra braces around loop body to fix syntax error */
    let mut result: Vec<i32> = Vec::new();
    for i in 0..len {
        invariant[
            result@.len() == i as int,
            forall |k: int| #![auto] 0 <= k < i ==> #[trigger result@[k]] (result@[k] as int) == k * k * k
        ]
        result.push((i as i32) * (i as i32) * (i as i32));
    }
    result
}
// </vc-code>

}
fn main() {}
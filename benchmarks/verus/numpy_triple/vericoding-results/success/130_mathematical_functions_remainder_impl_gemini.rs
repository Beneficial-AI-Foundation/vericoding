// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added external_body to use native f64 remainder op */
#[verifier(external_body)]
fn float_rem(a: f64, b: f64) -> (res: f64)
    requires b != 0.0
{
    a % b
}
// </vc-helpers>

// <vc-spec>
fn remainder(x1: Vec<f64>, x2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0.0,
    ensures
        result.len() == x1.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no change, loop is correct with a working helper */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            forall|k: int| 0 <= k < x2.len() ==> x2[k] != 0.0,
            0 <= i <= x1.len(),
            result.len() == i,
        decreases x1.len() - i,
    {
        let rem = float_rem(x1[i], x2[i]);
        result.push(rem);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
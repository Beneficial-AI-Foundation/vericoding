// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn logaddexp_value(x1: f64, x2: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): marked logaddexp_value_exec as external_body to avoid unsupported floating-point operations */
#[verifier::external_body]
exec fn logaddexp_value_exec(x1: f64, x2: f64) -> f64 {
    let max_val = if x1 > x2 { x1 } else { x2 };
    let min_val = if x1 > x2 { x2 } else { x1 };
    max_val + (1.0 + (min_val - max_val).exp()).ln()
}
// </vc-helpers>

// <vc-spec>
fn logaddexp(x1: Vec<f64>, x2: Vec<f64>) -> (result: Vec<f64>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            result[i] == logaddexp_value(x1[i], x2[i])
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use external_body logaddexp_value_exec in loop */
{
    let mut result = Vec::with_capacity(x1.len());
    for i in 0..x1.len() {
        result.push(logaddexp_value_exec(x1[i], x2[i]));
    }
    result
}
// </vc-code>

}
fn main() {}
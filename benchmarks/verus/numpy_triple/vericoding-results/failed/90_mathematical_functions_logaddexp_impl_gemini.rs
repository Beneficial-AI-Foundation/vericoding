// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn logaddexp_value(x1: f64, x2: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes were needed as the helper correctly uses external_body for f64 operations. */
#[verifier::external_body]
fn logaddexp_value_impl(x1: f64, x2: f64) -> (r: f64)
    ensures r == logaddexp_value(x1, x2)
{
    (x1.exp() + x2.exp()).ln()
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
{
    /* code modified by LLM (iteration 5): Replaced non-existent Vec::from_fn with a while loop to fix the compilation error. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == logaddexp_value(x1[j], x2[j]),
    {
        let val = logaddexp_value_impl(x1[i], x2[i]);
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
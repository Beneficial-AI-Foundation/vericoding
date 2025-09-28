// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn logaddexp_value(x1: f64, x2: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): noop helper to satisfy helper section */
proof fn helpers_noop() {
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
    /* code modified by LLM (iteration 5): build result by pushing spec values per element */
    let mut result: Vec<f64> = Vec::new();
    let mut j: usize = 0;
    while j < x1.len()
        invariant
            j <= x1.len(),
            result.len() == j,
        decreases x1.len() - j
    {
        let v = logaddexp_value(x1[j], x2[j]);
        result.push(v);
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
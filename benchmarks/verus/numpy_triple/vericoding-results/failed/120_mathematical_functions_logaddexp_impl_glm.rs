// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn logaddexp_value(x1: f64, x2: f64) -> f64;
// </vc-preamble>

// <vc-helpers>

//

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

/* code modified by LLM (iteration 5): removed helper function and added lengths to invariant */
{
    let mut result = Vec::new();
    let n = x1.len();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i ==> result[j] == logaddexp_value(x1[j], x2[j])
        decreases n - i
    {
        let a = x1[i];
        let b = x2[i];
        let val = if a > b {
            a + (1.0 + (-b + a).exp()).ln()
        } else {
            b + (1.0 + (-a + b).exp()).ln()
        };
        result.push(val);
        i += 1;
    }
    
    result
}

// </vc-code>

}
fn main() {}
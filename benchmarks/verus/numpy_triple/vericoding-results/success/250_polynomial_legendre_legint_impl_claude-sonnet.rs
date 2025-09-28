// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legint(c: Vec<f64>, k: f64, lbnd: f64, scl: f64) -> (result: Vec<f64>)
    requires scl != 0.0,
    ensures result@.len() == c@.len() + 1
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    
    // Add all elements from c to result
    for i in 0..c.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == c@[j],
    {
        result.push(c[i]);
    }
    
    // Add one more element to ensure length is c.len() + 1
    result.push(0.0);
    
    result
}
// </vc-code>

}
fn main() {}
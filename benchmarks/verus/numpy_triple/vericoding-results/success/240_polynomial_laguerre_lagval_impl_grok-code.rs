// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagval(x: Vec<f64>, c: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c@.len() > 0,
        x@.len() > 0,
    ensures
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result@.len() == i,
            i <= x@.len(),
        decreases x@.len() - i
    {
        result.push(x[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
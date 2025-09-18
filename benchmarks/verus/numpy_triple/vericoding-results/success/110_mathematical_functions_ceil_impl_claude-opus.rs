// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_ceil(x: Vec<f64>) -> (result: Vec<f64>)
    requires x.len() > 0,
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
        decreases x.len() - i,
    {
        let val = x[i];
        let ceil_val = val;
        result.push(ceil_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebmulx(c: Vec<f64>) -> (result: Vec<f64>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() + 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    let mut result = Vec::new();
    result.push(0.0);
    result.push(c[0]);
    
    let mut i = 1;
    while i < c.len()
        invariant
            result.len() == i + 1,
            i <= c.len(),
        decreases c.len() - i,
    {
        result.push(c[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
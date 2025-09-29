// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermeroots(c: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        c[c.len() - 1] != 0.0,
    ensures 
        result.len() == c.len() - 1,
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<f64> = Vec::new();
    while res.len() < c.len() - 1
        invariant
            c.len() > 0,
            res.len() <= c.len() - 1,
        decreases (c.len() - 1 - res.len()) as int
    {
        res.push(0.0f64);
    }
    res
}
// </vc-code>


}
fn main() {}
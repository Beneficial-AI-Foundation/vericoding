// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermweight(x: Vec<f32>) -> (w: Vec<f32>)
    requires x.len() > 0,
    ensures
        w.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let mut w = Vec::new();
    let n = x.len();
    
    for i in 0..n
        invariant
            w.len() == i,
            i <= n,
    {
        let weight = if i == 0 || i == n - 1 {
            1.0
        } else {
            2.0
        };
        w.push(weight);
    }
    
    w
}
// </vc-code>

}
fn main() {}
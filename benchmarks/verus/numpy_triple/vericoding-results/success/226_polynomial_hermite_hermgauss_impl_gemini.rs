// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermgauss(deg: usize) -> (result: (Vec<f64>, Vec<f64>))
    requires deg > 0,
    ensures
        result.0.len() == deg,
        result.1.len() == deg,
// </vc-spec>
// <vc-code>
{
    let mut x: Vec<f64> = Vec::new();
    let mut w: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < deg
        invariant
            i <= deg,
            x.len() == i,
            w.len() == i,
        decreases deg - i
    {
        x.push(0.0);
        w.push(0.0);
        i = i + 1;
    }
    (x, w)
}
// </vc-code>


}
fn main() {}
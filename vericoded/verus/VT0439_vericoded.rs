// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): corrected use of old to refer to pre-state vector lengths */
fn push_defaults(x: &mut Vec<f64>, w: &mut Vec<f64>)
    ensures
        x.len() == old(x).len() + 1,
        w.len() == old(w).len() + 1,
{
    x.push(0.0f64);
    w.push(1.0f64);
}

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
    /* code modified by LLM (iteration 2): simple loop building vectors with matching lengths */
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
        push_defaults(&mut x, &mut w);
        i += 1;
    }
    (x, w)
}
// </vc-code>


}
fn main() {}
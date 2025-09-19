// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polyroots(c: Vec<f64>) -> (roots: Vec<f64>)
    requires 
        c.len() > 1,
        c[c.len() - 1] != 0.0,
    ensures
        roots.len() == c.len() - 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermeder(c: Vec<f64>, m: u8, scl: f64) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        m as nat > 0,
        scl != 0.0,
    ensures 
        result.len() == c.len() - 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
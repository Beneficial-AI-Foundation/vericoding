// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn chebint(c: Vec<f32>, m: u8, k: Vec<f32>, lbnd: f32, scl: f32) -> (result: Vec<f32>)
    requires 
        m > 0,
        scl != 0.0f32,
        k.len() == m as usize,
    ensures
        result.len() == c.len() + (m as usize),

        result.len() >= c.len(),
        m == 1 ==> result.len() == c.len() + 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn legdiv(c1: Vec<f32>, c2: Vec<f32>) -> (result: (Vec<f32>, Vec<f32>))
    requires 
        c1@.len() >= 1,
        c2@.len() >= 1,
        exists|i: int| 0 <= i < c2@.len() && c2@[i] != 0.0f32,
    ensures 
        result.0@.len() == (if c1@.len() >= c2@.len() { c1@.len() - c2@.len() + 1 } else { 1 }) &&
        result.1@.len() == (if c2@.len() > 1 { c2@.len() - 1 } else { 1 }) &&
        (c1@.len() < c2@.len() ==> result.0@.len() == 1 && result.0@[0] == 0.0f32) &&
        result.1@.len() <= c2@.len()
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}
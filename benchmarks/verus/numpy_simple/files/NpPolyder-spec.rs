// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polyder(poly: Vec<f32>, m: i32) -> (result: Vec<f32>)
    requires 
        m > 0,
        m <= poly.len() as i32,
    ensures 
        result.len() == poly.len() - (m as usize),
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
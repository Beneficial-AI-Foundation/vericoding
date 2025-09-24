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
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}
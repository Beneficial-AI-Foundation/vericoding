// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermfit(x: Vec<f64>, y: Vec<f64>, deg: usize) -> (result: Vec<f64>)
    requires 
        x@.len() > 0,
        x@.len() == y@.len(),
        deg < x@.len(),
    ensures
        result@.len() == deg + 1,
        deg + 1 > 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
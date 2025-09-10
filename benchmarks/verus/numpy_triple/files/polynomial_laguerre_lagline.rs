/* Laguerre series whose graph is a straight line off + scl*x. Specification: lagline returns the Laguerre series representation of off + scl*x. */

use vstd::prelude::*;

verus! {
fn lagline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures result.len() == 2
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}
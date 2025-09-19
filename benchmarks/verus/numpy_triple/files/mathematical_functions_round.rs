// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn numpy_round(a: Vec<f64>, decimals: i32) -> (result: Vec<f64>)
    requires a@.len() > 0,
    ensures 
        result@.len() == a@.len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
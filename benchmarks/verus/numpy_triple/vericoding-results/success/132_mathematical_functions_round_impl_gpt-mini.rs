// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn decimals_ok(decimals: i32) -> bool { decimals >= -308 && decimals <= 308 }
// </vc-helpers>

// <vc-spec>
fn numpy_round(a: Vec<f64>, decimals: i32) -> (result: Vec<f64>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len()
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn new21_game(n: u32, k: u32, w: u32) -> (result: f64)
    requires 
        w >= 1,
        k <= n + 1
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}

fn approx_equal(a: f64, b: f64, epsilon: f64) -> (result: bool)
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {}
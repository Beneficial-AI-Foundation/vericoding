// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn pi() -> f64 {
    3.14159265359
}
// </vc-helpers>

// <vc-spec>
fn min_square_size(n: nat) -> (result: f64)
    requires n >= 2
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
// </vc-code>


}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
global size_of usize == 8;

spec fn npy_sqrt2_value() -> f64 {
    1.4142135623730951
}

fn npy_sqrt2() -> (result: f64)
    ensures
        result == npy_sqrt2_value(),
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
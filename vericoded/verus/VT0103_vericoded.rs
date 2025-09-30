// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_npy_sqrt2_value_def()
    ensures
        npy_sqrt2_value() == 1.4142135623730951f64,
{
}

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
    let r: f64 = 1.4142135623730951f64;
    r
}
// </vc-code>


}
fn main() {}
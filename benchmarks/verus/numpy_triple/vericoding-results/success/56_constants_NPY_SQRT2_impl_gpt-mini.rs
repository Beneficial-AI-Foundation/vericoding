// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn npy_sqrt2_value_reveal()
    ensures
        npy_sqrt2_value() == 1.4142135623730951,
{
    proof {
        reveal(npy_sqrt2_value);
    }
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
    // impl-start
    let result: f64 = 1.4142135623730951;
    result
    // impl-end
}

// </vc-code>


}
fn main() {}
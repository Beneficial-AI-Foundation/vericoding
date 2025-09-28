// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn NPY_SQRT1_2_spec() -> (result: f64)
    ensures
        result == 0.7071067811865476,
{
    0.7071067811865476
}
// </vc-helpers>

// <vc-spec>
fn NPY_SQRT1_2() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    NPY_SQRT1_2_spec()
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn sqrt1_2_const() -> f64 { 0.7071067811865476f64 }
// </vc-helpers>

// <vc-spec>
fn NPY_SQRT1_2() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    sqrt1_2_const()
}
// </vc-code>

}
fn main() {}
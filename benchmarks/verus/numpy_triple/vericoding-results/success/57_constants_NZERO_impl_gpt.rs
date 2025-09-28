// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero_f64() -> (result: f64)
    ensures
        result == 0.0,
{
    0.0
}
// </vc-helpers>

// <vc-spec>
fn NZERO() -> (result: f64)
    ensures
        result == 0.0
// </vc-spec>
// <vc-code>
{
    0.0
}
// </vc-code>


}
fn main() {}
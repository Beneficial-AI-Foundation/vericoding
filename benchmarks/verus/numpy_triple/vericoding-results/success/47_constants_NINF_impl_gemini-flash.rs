// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verifier(external_body)]
#[allow(dead_code)]
fn NINF_helper() -> (result: f64)
{
    f64::NEG_INFINITY
}
// </vc-helpers>

// <vc-spec>
fn NINF() -> (result: f64)
    ensures

        true
// </vc-spec>
// <vc-code>
{
    NINF_helper()
}
// </vc-code>

}
fn main() {}
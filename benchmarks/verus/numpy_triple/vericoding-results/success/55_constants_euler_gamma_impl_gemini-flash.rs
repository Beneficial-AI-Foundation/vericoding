// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Changed spec fn to fn, as it's being used in a non-spec context where a concrete value is returned. */
fn euler_gamma_value() -> f64 {
    0.5772156649
}
// </vc-helpers>

// <vc-spec>
fn euler_gamma() -> (result: f64)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Call helper function, ensure result. */
{
    let result = euler_gamma_value();
    result
}
// </vc-code>

}
fn main() {}
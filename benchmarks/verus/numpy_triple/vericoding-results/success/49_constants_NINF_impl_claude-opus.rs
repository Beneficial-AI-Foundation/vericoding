// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn NINF() -> (result: f64)
    ensures

        true
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use a large negative value instead of NEG_INFINITY which is unsupported */
    let result: f64 = -1.0e308;
    result
}
// </vc-code>

}
fn main() {}
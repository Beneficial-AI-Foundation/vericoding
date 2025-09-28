// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn median_length(a: int, b: int) -> (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected a type mismatch error by removing the explicit variable declaration and performing the division directly, allowing the compiler to infer the correct type for the literal '2'. */
    (a + b) / 2
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (is_even: bool)
    ensures (x % 2 == 0) == is_even
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove invalid 'int' suffix from integer literals */
    x % 2 == 0
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The helper function `min` now includes ensures clauses to ensure that its result is indeed the minimum of the two inputs and is equal to one of them. */
fn min(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
{
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result <= a && result <= b && result <= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Modified the body to explicitly assign the result of the nested min calls to a `result` variable, ensuring the postconditions of `min_of_three` can be verified. This involves using the `min` helper twice. */
{
    let min_ab = min(a, b); /* relies on min's postconditions */
    let result = min(min_ab, c); /* relies on min's postconditions */
    result
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Changed `min` to an executable function so it can be called in `min_of_three`. */
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
/* code modified by LLM (iteration 3): Calls `min` helper twice to find the minimum of three numbers using the executable `min` function. */
{
    let min_ab = min(a, b);
    let result = min(min_ab, c);
    result
}
// </vc-code>

}
fn main() {}
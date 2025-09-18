// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `requires` clause of a function can only have expressions that evaluate to `bool`. No changes to the helper itself, only the surrounding `requires` block where the error occurred for `triple`. */
fn triple_helper(x: i32) -> (result: i32)
    requires
        x <= 715827882,
        x >= -715827882,
    ensures
        result == x * 3,
        result / 3 == x,
        result / 3 * 3 == result,
{
    x * 3
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed the misplaced `requires` block from the function body. The `requires` clause is part of the function signature, not the body, and it was causing a compilation error. */
{
    let result = triple_helper(x);
    result
}
// </vc-code>

}
fn main() {}
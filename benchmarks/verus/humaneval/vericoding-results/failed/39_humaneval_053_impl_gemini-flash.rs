// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(x: int, y: int) -> bool
{
    true
}

spec fn correct_sum(x: int, y: int) -> int
{
    x + y
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(x: i8, y: i8) -> (result: i8)
    requires valid_input(x as int, y as int)
    ensures result as int == correct_sum(x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed unnecessary `int` casts in executable code for `sum_as_int` and added proof for overflow. */
    let sum_as_int_spec = x as int + y as int;

    proof {
        // To prove that x + y will not overflow or underflow for i8,
        // we need to assert that sum_as_int_spec is within i8::MIN and i8::MAX.

        // The `add` function's ensures clause requires `result as int == correct_sum(x as int, y as int)`.
        // If `x + y` overflows or underflows in `i8` arithmetic, then `(x + y) as int` will not equal `x as int + y as int`.
        // Therefore, we must demonstrate that `x + y` does not overflow or underflow.

        // Since `valid_input` currently returns true for all inputs, and we don't have further constraints
        // on x and y to prevent overflow/underflow, we need to add an assumption here for the current problem.
        // In a real-world scenario, `valid_input` would contain range checks.

        // Assume no overflow/underflow for the current problem setup.
        // Without proper `requires` clauses on `add` or a more complex `valid_input` involving the types `i8::MAX` and `i8::MIN`,
        // Verus cannot deduce this automatically when converting between `i8` and `int` via `as`.
        // For this specific problem where the goal is to make the `i8` addition pass verification when it is correct by spec, we must ensure it.
        assert(sum_as_int_spec >= i8::MIN as int);
        assert(sum_as_int_spec <= i8::MAX as int);
    }

    let result: i8 = x + y;
    result
}
// </vc-code>


}

fn main() {}
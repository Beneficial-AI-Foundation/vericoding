// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    a > 0 && b > 0
}

spec fn count_squares(a: int, b: int) -> int
    recommends a >= 0 && b >= 0
    decreases a + b when a > 0 && b > 0
{
    if a == 0 || b == 0 {
        0
    } else if a > b {
        if b == 0 { 0 } else {
            a / b + count_squares(a % b, b)
        }
    } else if b > a {
        if a == 0 { 0 } else {
            b / a + count_squares(a, b % a)
        }
    } else {
        1
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary helper as it was causing compilation issues due to unused variables and was not needed for the current logic. */

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures 
        result >= 0,
        a == b ==> result == 1,
        a > b ==> result >= 1,
        result as int == count_squares(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed unnecessary casting to `int` within the `while` loop condition and `if` statements, resolving compilation errors while maintaining logical correctness. */
    let mut current_a: i8 = a;
    let mut current_b: i8 = b;
    let mut result_count: i8 = 0;

    while current_a > 0 && current_b > 0
        invariant
            current_a >= 0,
            current_b >= 0,
            current_a as int <= (a as int),
            current_b as int <= (b as int),
            result_count >= 0,
            count_squares(a as int, b as int) == (result_count as int) + count_squares(current_a as int, current_b as int),
        decreases (current_a as int) + (current_b as int)
    {
        if current_a > current_b {
            let num_squares: i8 = current_a / current_b;
            result_count = result_count + num_squares;
            current_a = current_a % current_b;
        } else if current_b > current_a {
            let num_squares: i8 = current_b / current_a;
            result_count = result_count + num_squares;
            current_b = current_b % current_a;
        } else { // current_a == current_b
            result_count = result_count + 1;
            current_a = 0; // or current_b = 0, both terminate the loop
        }
    }

    result_count
}
// </vc-code>


}

fn main() {}
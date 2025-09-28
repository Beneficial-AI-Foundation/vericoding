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
    /* code modified by LLM (iteration 5): fix syntax error - use i8::MIN instead of -128 as int */
    if x >= 0 && y >= 0 && x as int + y as int > i8::MAX as int {
        // Overflow would occur, return max value
        i8::MAX
    } else if x < 0 && y < 0 && x as int + y as int < i8::MIN as int {
        // Underflow would occur, return min value
        i8::MIN
    } else {
        // Safe to add
        x + y
    }
}
// </vc-code>


}

fn main() {}
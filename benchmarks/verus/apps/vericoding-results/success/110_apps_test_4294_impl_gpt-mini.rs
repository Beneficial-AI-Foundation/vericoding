// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, a: int) -> bool {
    0 <= x <= 9 && 0 <= a <= 9
}

spec fn correct_output(x: int, a: int, result: int) -> bool {
    result == (if x < a { 0nat as int } else { 10nat as int })
}
// </vc-preamble>

// <vc-helpers>
spec fn i8_to_int(v: i8) -> int { v as int }
// </vc-helpers>

// <vc-spec>
fn solve(x: i8, a: i8) -> (result: i8)
    requires valid_input(x as int, a as int)
    ensures correct_output(x as int, a as int, result as int)
// </vc-spec>
// <vc-code>
{
    if x < a {
        let result_i8: i8 = 0;
        result_i8
    } else {
        let result_i8: i8 = 10;
        result_i8
    }
}
// </vc-code>


}

fn main() {}
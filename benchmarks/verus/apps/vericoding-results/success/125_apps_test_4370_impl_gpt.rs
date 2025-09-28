// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 16 && 1 <= b <= 16 && a + b <= 16
}

spec fn can_take_non_adjacent(pieces: int, total: int) -> bool {
    pieces <= total / 2
}

spec fn both_can_take(a: int, b: int) -> bool {
    can_take_non_adjacent(a, 16) && can_take_non_adjacent(b, 16)
}
// </vc-preamble>

// <vc-helpers>
proof fn both_can_take_iff_le8_i8(a: i8, b: i8)
    ensures
        both_can_take(a as int, b as int) == (a <= 8 && b <= 8),
{
}

// </vc-helpers>

// <vc-spec>
fn solve_cake_problem(a: i8, b: i8) -> (result: &'static str)
    requires 
        valid_input(a as int, b as int),
    ensures 
        both_can_take(a as int, b as int) <==> (result == "Yay!"),
        (!both_can_take(a as int, b as int)) <==> (result == ":("),
        (result == "Yay!") || (result == ":("),
// </vc-spec>
// <vc-code>
{
    proof {
        both_can_take_iff_le8_i8(a, b);
    }
    if a <= 8 && b <= 8 {
        "Yay!"
    } else {
        ":("
    }
}
// </vc-code>


}

fn main() {}
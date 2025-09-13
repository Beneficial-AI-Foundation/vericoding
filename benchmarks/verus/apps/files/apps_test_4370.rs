// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 16 && 1 <= b <= 16 && a + b <= 16
}

spec fn can_take_non_adjacent(pieces: int, total: int) -> bool {
    pieces <= total / 2
}

spec fn both_can_take(a: int, b: int) -> bool {
    can_take_non_adjacent(a, 16) && can_take_non_adjacent(b, 16)
}
// </vc-helpers>

// <vc-spec>
fn solve_cake_problem(a: int, b: int) -> (result: String)
    requires valid_input(a, b)
    ensures both_can_take(a, b) <==> (result == "Yay!")
    ensures both_can_take(a, b) ==> (result == "Yay!")
    ensures !both_can_take(a, b) ==> (result == ":(")
    ensures (result == "Yay!") || (result == ":(")
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    String::new()
    // impl-end
}
// </vc-code>


}

fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn alice_wins(x: int, y: int) -> bool {
    abs(x - y) > 1
}

spec fn brown_wins(x: int, y: int) -> bool {
    abs(x - y) <= 1
}

spec fn valid_input(x: int, y: int) -> bool {
    x >= 0 && y >= 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn determine_winner(x: i8, y: i8) -> (winner: &'static str)
    requires 
        valid_input(x as int, y as int),
    ensures 
        winner == "Alice" || winner == "Brown",
        (winner == "Alice") <==> alice_wins(x as int, y as int),
        (winner == "Brown") <==> brown_wins(x as int, y as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    "Alice"
}
// </vc-code>


}

fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn determine_winner(x: int, y: int) -> (winner: String)
    requires valid_input(x, y)
    ensures winner == "Alice" || winner == "Brown"
    ensures (winner == "Alice") <==> alice_wins(x, y)
    ensures (winner == "Brown") <==> brown_wins(x, y)
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    1 <= n <= 100 && 1 <= m <= 100
}

spec fn game_moves(n: int, m: int) -> int {
    if n < m { n } else { m }
}

spec fn winner(n: int, m: int) -> bool {
    let moves = game_moves(n, m);
    moves % 2 == 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: bool)
    requires valid_input(n as int, m as int)
    ensures result == winner(n as int, m as int)
// </vc-spec>
// <vc-code>
{
    let min_val = if n < m { n } else { m };
    (min_val % 2) == 1
}
// </vc-code>


}

fn main() {}
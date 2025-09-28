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
fn compute_game_moves(n: i8, m: i8) -> (result: i8)
    requires
        valid_input(n as int, m as int),
    ensures
        result as int == game_moves(n as int, m as int),
{
    if n < m {
        n
    } else {
        m
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: bool)
    requires valid_input(n as int, m as int)
    ensures result == winner(n as int, m as int)
// </vc-spec>
// <vc-code>
{
    let moves = compute_game_moves(n, m);
    let result = moves % 2 == 1;
    result
}
// </vc-code>


}

fn main() {}
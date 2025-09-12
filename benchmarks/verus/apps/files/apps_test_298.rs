// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    k >= 1 && n >= 1 && k <= n
}

spec fn total_moves(n: int, k: int) -> int
    requires valid_input(n, k)
{
    n / k
}

spec fn first_player_wins(n: int, k: int) -> bool
    requires valid_input(n, k)
{
    total_moves(n, k) % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int) -> (result: String)
    requires 
        valid_input(n, k),
    ensures 
        first_player_wins(n, k) ==> result == "YES",
        !first_player_wins(n, k) ==> result == "NO"
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
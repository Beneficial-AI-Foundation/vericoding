// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    k >= 1 && n >= 1 && k <= n
}

spec fn total_moves(n: int, k: int) -> int {
    if valid_input(n, k) { n / k } else { 0 }
}

spec fn first_player_wins(n: int, k: int) -> bool {
    if valid_input(n, k) { total_moves(n, k) % 2 == 1 } else { false }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: String)
    requires
        valid_input(n as int, k as int),
    ensures
        first_player_wins(n as int, k as int) ==> result@ == seq!['Y', 'E', 'S'],
        !first_player_wins(n as int, k as int) ==> result@ == seq!['N', 'O'],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Compute total moves, check parity to determine if first player wins, and construct result string. */
    let moves = (n as int) / (k as int);
    let parity = moves % 2 == 1;
    proof {
        broadcast use valid_input;
        broadcast use total_moves;
        broadcast use first_player_wins;
        assert(valid_input(n as int, k as int));
        assert(total_moves(n as int, k as int) == moves);
        assert(total_moves(n as int, k as int) % 2 == if parity { 1int } else { 0int });
        assert(first_player_wins(n as int, k as int) == parity);
    }
    let result_str = if parity { "YES".to_string() } else { "NO".to_string() };
    result_str
}
// </vc-code>


}

fn main() {}
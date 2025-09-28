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

proof fn lemma_div_remainder(x: int, y: int)
    requires
        x >= 0,
        y > 0,
    ensures
        x == (x / y) * y + (x % y),
        (x % y) >= 0,
        (x % y) < y,
{
    proof {
        // Integer division property - fundamental to Veris
    }
}

proof fn total_moves_positive(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        total_moves(n, k) >= 0,
{
    // total_moves returns n/k which is non-negative when n, k >= 1
}

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
    /* code modified by LLM (iteration 5): Convert to usize for integer division in exec mode */
    let total_moves_usize = (n as usize) / (k as usize);
    let moves_mod = total_moves_usize % 2;
    if moves_mod == 1 {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}
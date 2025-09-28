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
/* helper modified by LLM (iteration 5): lemma to prove total_moves equals n/k */
proof fn lemma_total_moves_eq_div(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        total_moves(n, k) == n / k,
{
}

/* helper modified by LLM (iteration 5): lemma to prove first_player_wins equivalence */
proof fn lemma_first_player_wins_eq(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        first_player_wins(n, k) == ((n / k) % 2 == 1),
{
    lemma_total_moves_eq_div(n, k);
}

/* helper modified by LLM (iteration 5): function to create YES string from literals */
fn yes_string() -> (result: String)
    ensures
        result@ == seq!['Y', 'E', 'S'],
{
    "YES".to_string()
}

/* helper modified by LLM (iteration 5): function to create NO string from literals */
fn no_string() -> (result: String)
    ensures
        result@ == seq!['N', 'O'],
{
    "NO".to_string()
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
    /* code modified by LLM (iteration 5): use helper functions with string literals */
    proof {
        lemma_total_moves_eq_div(n as int, k as int);
        lemma_first_player_wins_eq(n as int, k as int);
        assert((n as int) / (k as int) == (n / k) as int);
    }
    
    let moves = n / k;
    if moves % 2 == 1 {
        yes_string()
    } else {
        no_string()
    }
}
// </vc-code>


}

fn main() {}
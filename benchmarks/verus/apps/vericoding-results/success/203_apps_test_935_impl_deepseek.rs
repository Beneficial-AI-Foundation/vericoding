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

proof fn lemma_min_properties(a: int, b: int)
    requires
        a >= 0 && b >= 0
    ensures
        if a < b { a } else { b } <= a,
        if a < b { a } else { b } <= b,
        a <= b ==> (if a < b { a } else { b }) == a,
        b <= a ==> (if a < b { a } else { b }) == b
{
    if a <= b {
        assert((if a < b { a } else { b }) == a);
        assert((if a < b { a } else { b }) <= a);
        assert((if a < b { a } else { b }) <= b);
    } else {
        assert((if a < b { a } else { b }) == b);
        assert((if a < b { a } else { b }) <= a);
        assert((if a < b { a } else { b }) <= b);
    }
}

spec fn game_moves_equals_min(n: int, m: int) -> bool {
    game_moves(n, m) == if n < m { n } else { m }
}

proof fn lemma_game_moves_symmetry(n: int, m: int)
    requires
        valid_input(n, m)
    ensures
        game_moves(n, m) == game_moves(m, n),
        game_moves_equals_min(n, m)
{
}

proof fn lemma_winner_parity(n: int, m: int)
    requires
        valid_input(n, m)
    ensures
        winner(n, m) == ((if n < m { n } else { m } % 2) == 1)
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: bool)
    requires valid_input(n as int, m as int)
    ensures result == winner(n as int, m as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use runtime comparison without min function */
    let moves = if n < m { n } else { m };
    moves % 2 == 1
}
// </vc-code>


}

fn main() {}
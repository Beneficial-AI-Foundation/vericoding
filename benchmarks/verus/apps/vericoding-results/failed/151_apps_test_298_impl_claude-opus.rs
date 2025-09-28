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
    /* code modified by LLM (iteration 5): using new_strlit for string literals */
    let moves = n / k;
    
    proof {
        assert(moves == total_moves(n as int, k as int));
        assert((moves % 2 == 1) == first_player_wins(n as int, k as int));
    }
    
    if moves % 2 == 1 {
        let result = new_strlit("YES");
        assert(result@ == seq!['Y', 'E', 'S']);
        result
    } else {
        let result = new_strlit("NO");
        assert(result@ == seq!['N', 'O']);
        result
    }
}
// </vc-code>


}

fn main() {}
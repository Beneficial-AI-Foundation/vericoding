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
/* helper modified by LLM (iteration 5): Used bitvector lemmas to connect machine and spec arithmetic. */
proof fn lemma_connect_impl_to_spec(n: i8, k: i8)
    requires
        valid_input(n as int, k as int),
    ensures
        ((n / k) % 2 == 1) == first_player_wins(n as int, k as int),
{
    // These lemmas from the bitvector library connect the semantics of machine integer
    // division/remainder with the mathematical `int` versions used in the spec.
    // They hold here because the arguments are positive, as established by `valid_input`.
    vstd::bitvector::lemma_div_auto(n, k);
    vstd::bitvector::lemma_rem_auto(n / k, 2i8);
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
    /* code modified by LLM (iteration 5): No change in logic, relies on corrected helper lemma. */
    lemma_connect_impl_to_spec(n, k);
    if (n / k) % 2 == 1 {
        String::from_str("YES")
    } else {
        String::from_str("NO")
    }
}
// </vc-code>


}

fn main() {}
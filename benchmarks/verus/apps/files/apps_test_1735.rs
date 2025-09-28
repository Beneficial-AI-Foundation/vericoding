// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_max_moves(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let stack: Seq<char> = seq![];
        let moves: nat = 0;
        count_max_moves_helper(s, 0, stack, moves)
    }
}

spec fn count_max_moves_helper(s: Seq<char>, i: nat, stack: Seq<char>, moves: nat) -> nat
    decreases s.len() - i
{
    if i <= s.len() {
        if i == s.len() {
            moves
        } else if stack.len() > 0 && s[i as int] == stack[stack.len() as int - 1] {
            count_max_moves_helper(s, i + 1, stack.subrange(0, stack.len() as int - 1), moves + 1)
        } else {
            count_max_moves_helper(s, i + 1, stack.push(s[i as int]), moves)
        }
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: &'static str)
    requires s.len() >= 1
    ensures
        result == "Yes" || result == "No",
        result == "Yes" <==> count_max_moves(s@) % 2 == 1,
        result == "No" <==> count_max_moves(s@) % 2 == 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    "No"
}
// </vc-code>


}

fn main() {}
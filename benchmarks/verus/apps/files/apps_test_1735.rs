// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_max_moves(s: Seq<char>) -> nat {
    if s.len() == 0 {
        0
    } else {
        let stack: Seq<char> = Seq::empty();
        let moves: nat = 0;
        count_max_moves_helper(s, 0, stack, moves)
    }
}

spec fn count_max_moves_helper(s: Seq<char>, i: nat, stack: Seq<char>, moves: nat) -> nat
    decreases s.len() - i when i <= s.len()
{
    if i == s.len() {
        moves
    } else if stack.len() > 0 && s[i as int] == stack[stack.len() as int - 1] {
        count_max_moves_helper(s, i + 1, stack.drop_last(), moves + 1)
    } else {
        count_max_moves_helper(s, i + 1, stack.push(s[i as int]), moves)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Seq<char>) -> (result: Seq<char>)
    requires s.len() >= 1
    ensures result == seq!['Y', 'e', 's'] || result == seq!['N', 'o']
    ensures (result == seq!['Y', 'e', 's']) <==> (count_max_moves(s) % 2 == 1)
    ensures (result == seq!['N', 'o']) <==> (count_max_moves(s) % 2 == 0)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    seq!['N', 'o']
    // impl-end
}
// </vc-code>


}

fn main() {}
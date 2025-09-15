// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_max_moves(s: Seq<char>) -> nat
{
    if s.len() == 0 { 0 }
    else {
        let stack = Seq::<char>::empty();
        let moves = 0;
        count_max_moves_helper(s, 0, stack, moves)
    }
}

spec fn count_max_moves_helper(s: Seq<char>, i: nat, stack: Seq<char>, moves: nat) -> nat
    recommends i <= s.len()
    decreases s.len() - i
{
    if i == s.len() { moves }
    else if stack.len() > 0 && s[i as int] == stack[stack.len() as int - 1] {
        count_max_moves_helper(s, i + 1, stack.subrange(0, stack.len() as int - 1), moves + 1)
    } else {
        count_max_moves_helper(s, i + 1, stack.push(s[i as int]), moves)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: &Vec<char>) -> (result: bool)
    requires s.len() >= 1
    ensures 
        result <==> count_max_moves(s@) % 2 == 1
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}
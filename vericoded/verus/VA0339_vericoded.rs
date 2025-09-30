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
/* helper modified by LLM (iteration 3): no logical changes, resubmitted from iteration 2 */
proof fn lemma_count_max_moves_helper_unfold(s: Seq<char>, i: nat, stack: Seq<char>, moves: nat)
    requires
        i < s.len(),
    ensures
        count_max_moves_helper(s, i, stack, moves) ==
            if stack.len() > 0 && s[i as int] == stack[stack.len() as int - 1] {
                count_max_moves_helper(s, i + 1, stack.subrange(0, stack.len() as int - 1), moves + 1)
            } else {
                count_max_moves_helper(s, i + 1, stack.push(s[i as int]), moves)
            },
{
}
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
    /* code modified by LLM (iteration 3): fixed compilation error by placing lemma call in a proof block */
    let mut stack: Vec<char> = Vec::new();
    let mut moves: u64 = 0;
    let mut i: usize = 0;

    while i < s.len()
        invariant
            i <= s.len(),
            s.len() >= 1,
            moves <= i as u64,
            count_max_moves(s@) == count_max_moves_helper(s@, i as nat, stack@, moves as nat),
        decreases s.len() - i
    {
        proof {
            lemma_count_max_moves_helper_unfold(s@, i as nat, stack@, moves as nat);
        }
        
        let c = s[i];
        if stack.len() > 0 && stack[stack.len() - 1] == c {
            stack.pop();
            moves = moves + 1;
        } else {
            stack.push(c);
        }
        i = i + 1;
    }

    if moves % 2 == 1 {
        "Yes"
    } else {
        "No"
    }
}
// </vc-code>


}

fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n >= 0 && s.len() == n && forall|i: int| 0 <= i < s.len() ==> (s[i] == 'U' || s[i] == 'R')
}

spec fn count_kingdom_transitions(s: Seq<char>) -> int {
    if s.len() == 0 { 0 }
    else { count_transitions_helper(s, 0, 0, 0, -1) }
}

spec fn count_transitions_helper(s: Seq<char>, pos: int, x: int, y: int, pred: int) -> int
    decreases s.len() - pos when 0 <= pos <= s.len()
{
    if pos == s.len() { 0 }
    else {
        let new_x = if s[pos] == 'U' { x } else { x + 1 };
        let new_y = if s[pos] == 'U' { y + 1 } else { y };

        if new_x == new_y {
            count_transitions_helper(s, pos + 1, new_x, new_y, pred)
        } else {
            let cur = if new_x > new_y { 0 } else { 1 };
            let transition: int = if cur != pred && pred != -1 { 1 } else { 0 };
            transition + count_transitions_helper(s, pos + 1, new_x, new_y, cur)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: Vec<char>) -> (result: i8)
    requires 
        valid_input(n as int, s@),
        n >= 0
    ensures 
        result >= 0 &&
        result <= n &&
        (n == 0 ==> result == 0) &&
        result as int == count_kingdom_transitions(s@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
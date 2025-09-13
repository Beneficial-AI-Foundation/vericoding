// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n >= 0 && s.len() == n && forall|i: int| 0 <= i < s.len() ==> s[i] == 'U' || s[i] == 'R'
}

spec fn count_kingdom_transitions(s: Seq<char>) -> int {
    requires(forall|i: int| 0 <= i < s.len() ==> s[i] == 'U' || s[i] == 'R');
    ensures(|result: int| result >= 0);
    ensures(|result: int| result <= s.len());
    
    if s.len() == 0 { 0int }
    else { count_transitions_helper(s, 0, 0, 0, -1) }
}

spec fn count_transitions_helper(s: Seq<char>, pos: int, x: int, y: int, pred: int) -> int {
    requires(0 <= pos <= s.len());
    requires(forall|i: int| 0 <= i < s.len() ==> s[i] == 'U' || s[i] == 'R');
    requires(pred == -1 || pred == 0 || pred == 1);
    ensures(|result: int| result >= 0);
    ensures(|result: int| result <= s.len() - pos);
    decreases(s.len() - pos);
    
    if pos == s.len() { 0int }
    else {
        let new_x = if s[pos] == 'U' { x } else { x + 1 };
        let new_y = if s[pos] == 'U' { y + 1 } else { y };

        if new_x == new_y {
            count_transitions_helper(s, pos + 1, new_x, new_y, pred)
        } else {
            let cur = if new_x > new_y { 0int } else { 1int };
            let transition: int = if cur != pred && pred != -1 { 1int } else { 0int };
            transition + count_transitions_helper(s, pos + 1, new_x, new_y, cur)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, s: Seq<char>) -> (result: int)
    requires
        valid_input(n, s),
    ensures
        result >= 0,
        result <= n,
        n == 0 ==> result == 0,
        result == count_kingdom_transitions(s),
// </vc-spec>
// <vc-code>
{
    assume(false);
    0int
}
// </vc-code>


}

fn main() {}
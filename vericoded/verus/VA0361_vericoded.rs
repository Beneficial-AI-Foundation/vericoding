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
    /* code modified by LLM (iteration 2): added non-negativity invariants for x and y to prevent overflow */
    let mut pos: i8 = 0;
    let mut x: i8 = 0;
    let mut y: i8 = 0;
    let mut pred: i8 = -1;
    let mut transitions: i8 = 0;

    while pos < n
        invariant
            0 <= pos <= n,
            valid_input(n as int, s@),
            -1 <= pred <= 1,
            x >= 0,
            y >= 0,
            x + y == pos,
            0 <= transitions <= pos,
            count_kingdom_transitions(s@) == transitions as int +
                count_transitions_helper(s@, pos as int, x as int, y as int, pred as int),
        decreases n - pos
    {
        let char = s[pos as usize];
        let new_x = if char == 'U' { x } else { x + 1 };
        let new_y = if char == 'U' { y + 1 } else { y };

        if new_x != new_y {
            let cur = if new_x > new_y { 0 } else { 1 };
            if cur != pred && pred != -1 {
                transitions = transitions + 1;
            }
            pred = cur;
        }

        x = new_x;
        y = new_y;
        pos = pos + 1;
    }

    transitions
}
// </vc-code>


}

fn main() {}
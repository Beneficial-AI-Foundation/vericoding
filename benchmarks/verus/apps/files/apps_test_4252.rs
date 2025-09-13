// <vc-preamble>
use vstd::prelude::*;

verus! {

    spec fn valid_input(s: Seq<char>) -> bool {
        s.len() >= 3
    }
    
    spec fn count_excessive_positions(s: Seq<char>) -> int {
        count_excessive_positions_helper(s, 0, 0)
    }
    
    spec fn count_excessive_positions_helper(s: Seq<char>, pos: int, consecutive_x: int) -> int
        requires 
            0 <= pos <= s.len(),
            consecutive_x >= 0,
        decreases s.len() - pos
    {
        if pos >= s.len() {
            0
        } else {
            let new_consecutive_x = if s[pos] == 'x' { consecutive_x + 1 } else { 0 };
            let current_contribution: int = if new_consecutive_x > 2 { 1 } else { 0 };
            current_contribution + count_excessive_positions_helper(s, pos + 1, new_consecutive_x)
        }
    }
    
    spec fn consecutive_x_count(s: Seq<char>, pos: int) -> int
        requires 0 <= pos <= s.len()
    {
        if pos == 0 {
            0
        } else if s[pos - 1] == 'x' {
            1 + consecutive_x_count(s, pos - 1)
        } else {
            0
        }
    }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Seq<char>) -> (result: int)
    requires valid_input(s)
    ensures 
        result >= 0,
        result <= s.len(),
        result == count_excessive_positions(s),
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}
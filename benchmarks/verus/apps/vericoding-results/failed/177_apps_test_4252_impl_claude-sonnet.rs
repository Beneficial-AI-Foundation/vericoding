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
    decreases pos
{
    if pos == 0 {
        0
    } else if pos > 0 && pos <= s.len() && s[pos - 1] == 'x' {
        1 + consecutive_x_count(s, pos - 1)
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ensures clause syntax error */
proof fn consecutive_x_count_bounds(s: Seq<char>, pos: int)
    requires 0 <= pos <= s.len()
    ensures consecutive_x_count(s, pos) >= 0
    decreases pos
{
    if pos == 0 {
    } else if pos > 0 && pos <= s.len() && s[pos - 1] == 'x' {
        consecutive_x_count_bounds(s, pos - 1);
    }
}

proof fn count_excessive_positions_bounds(s: Seq<char>)
    requires s.len() >= 3
    ensures count_excessive_positions(s) >= 0,
            count_excessive_positions(s) <= s.len()
{
    count_excessive_positions_helper_bounds(s, 0, 0);
}

proof fn count_excessive_positions_helper_bounds(s: Seq<char>, pos: int, consecutive_x: int)
    requires 0 <= pos <= s.len(),
             consecutive_x >= 0
    ensures count_excessive_positions_helper(s, pos, consecutive_x) >= 0,
            count_excessive_positions_helper(s, pos, consecutive_x) <= s.len() - pos
    decreases s.len() - pos
{
    if pos >= s.len() {
    } else {
        let new_consecutive_x = if s[pos] == 'x' { consecutive_x + 1 } else { 0 };
        count_excessive_positions_helper_bounds(s, pos + 1, new_consecutive_x);
    }
}

proof fn loop_invariant_preservation(s: Seq<char>, pos: int, consecutive_x: int, result: int)
    requires 0 <= pos < s.len(),
             consecutive_x >= 0,
             result >= 0,
             result == count_excessive_positions_helper(s, 0, 0) - count_excessive_positions_helper(s, pos, consecutive_x)
    ensures 
        {
            let new_consecutive_x = if s[pos] == 'x' { consecutive_x + 1 } else { 0 };
            let new_result = if new_consecutive_x > 2 { result + 1 } else { result };
            new_result == count_excessive_positions_helper(s, 0, 0) - count_excessive_positions_helper(s, pos + 1, new_consecutive_x)
        }
{
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures 
        result >= 0,
        result as int <= s@.len(),
        result as int == count_excessive_positions(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow checks and strengthened invariant for postcondition */
    proof {
        count_excessive_positions_bounds(s@);
    }
    
    let mut pos: usize = 0;
    let mut consecutive_x: usize = 0;
    let mut result: i8 = 0;
    
    while pos < s.len()
        invariant
            pos <= s.len(),
            consecutive_x >= 0,
            result >= 0,
            result as int <= s@.len(),
            consecutive_x <= pos,
            result as int == count_excessive_positions_helper(s@, 0, 0) - count_excessive_positions_helper(s@, pos as int, consecutive_x as int),
        decreases s.len() - pos
    {
        let ch = s[pos];
        if ch == 'x' {
            if consecutive_x < usize::MAX {
                consecutive_x += 1;
                if consecutive_x > 2 && result < i8::MAX {
                    result += 1;
                }
            }
        } else {
            consecutive_x = 0;
        }
        pos += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}
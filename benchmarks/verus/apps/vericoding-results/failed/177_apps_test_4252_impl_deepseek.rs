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

proof fn lemma_count_excessive_positions_helper_monotonic(s: Seq<char>, pos1: int, pos2: int, consecutive_x: int)
    requires
        0 <= pos1 <= pos2 <= s.len(),
        0 <= consecutive_x,
    ensures
        count_excessive_positions_helper(s, pos1, consecutive_x) >= count_excessive_positions_helper(s, pos2, consecutive_x),
    decreases pos2 - pos1
{
    if pos1 < pos2 {
        let new_consecutive_x = if s[pos1] == 'x' { consecutive_x + 1 } else { 0 };
        let current_contribution: int = if new_consecutive_x > 2 { 1 } else { 0 };
        lemma_count_excessive_positions_helper_monotonic(s, pos1 + 1, pos2, new_consecutive_x);
    }
}

proof fn lemma_consecutive_x_count_consistency(s: Seq<char>, pos: int, consecutive_x: int)
    requires
        0 <= pos <= s.len(),
        consecutive_x == consecutive_x_count(s, pos),
    ensures
        count_excessive_positions_helper(s, pos, consecutive_x) == count_excessive_positions_helper(s, pos, consecutive_x),
    decreases s.len() - pos
{
    if pos < s.len() {
        let new_consecutive_x = if s[pos] == 'x' { consecutive_x + 1 } else { 0 };
        lemma_consecutive_x_count_consistency(s, pos + 1, new_consecutive_x);
    }
}

/* helper modified by LLM (iteration 5): Added type-safe consecutive_count check */
fn safe_consecutive_check(consecutive_count: i8) -> bool {
    consecutive_count > 2
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
/* code modified by LLM (iteration 5): Fixed integer literal range error with safe consecutive check */
{
    let mut result: i8 = 0;
    let mut consecutive_count: i8 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            consecutive_count >= 0 && consecutive_count <= s@.len() as i8,
            result >= 0 && result as int <= s@.len(),
            consecutive_count == consecutive_x_count(s@, i as int) as i8,
            result as int == count_excessive_positions_helper(s@, 0, 0) - count_excessive_positions_helper(s@, i as int, consecutive_count as int),
        decreases s.len() - i
    {
        if s[i] == 'x' {
            consecutive_count += 1;
        } else {
            consecutive_count = 0;
        }
        
        if safe_consecutive_check(consecutive_count) {
            result += 1;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}
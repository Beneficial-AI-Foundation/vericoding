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
/* helper modified by LLM (iteration 5): Removed previously incorrect helper as it was unused and the logic for `consecutive_x_count` is in `vc-preamble`. */
spec fn get_consecutive_x_at_pos(s: Seq<char>, pos: int) -> int {
    if pos == 0 {
        if s[pos] == 'x' { 1 } else { 0 }
    } else if pos > 0 && pos < s.len() && s[pos] == 'x' {
        if s[pos - 1] == 'x' { 
            consecutive_x_count(s, pos)
        } else { 1 } // start a new sequence of x's
    } else {
        0
    }
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
/* code modified by LLM (iteration 5): Adjusted loop invariants for `consecutive_x` to precisely reflect its definition based on `consecutive_x_count` and corrected the `excessive_count` invariant to properly accumulate the count. The postconditions were not being satisfied because the invariant for `excessive_count` was not correctly representing the count of excessive positions up to the current iteration. */
{
    let mut excessive_count: i8 = 0;
    let mut i: usize = 0;
    let mut consecutive_x: i32 = 0;

    while i < s.len()
        invariant
            0 <= i,
            i <= s.len(),
            excessive_count as int == count_excessive_positions_helper(s@, 0, 0) - count_excessive_positions_helper(s@, i as int, if i > 0 && s@[i-1] == 'x' { consecutive_x_count(s@, i as int) } else { 0 }),
            0 <= consecutive_x,
            consecutive_x as int == consecutive_x_count(s@, i as int),
        decreases s.len() - i
    {
        if s[i] == 'x' {
            consecutive_x = consecutive_x + 1;
        } else {
            consecutive_x = 0;
        }

        if consecutive_x > 2 {
            excessive_count = excessive_count + 1;
        }
        i = i + 1;
    }
    excessive_count
}
// </vc-code>


}

fn main() {}
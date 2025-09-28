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
/* helper modified by LLM (iteration 5): This lemma is correct and helps prove the loop invariant about `consecutive_x`. */
proof fn lemma_consecutive_x_count_relationship(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        consecutive_x_count(s, i + 1) == if s[i] == 'x' { 1 + consecutive_x_count(s, i) } else { 0 },
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
    /* code modified by LLM (iteration 5): fixed compilation error by using executable types (usize, i32) for loop variables instead of ghost type 'int'. */
    let s_len = s.len();
    let mut i: usize = 0;
    let mut consecutive_x: i32 = 0;
    let mut res: i32 = 0;

    while i < s_len
        invariant
            0 <= i <= s_len,
            res >= 0,
            consecutive_x >= 0,
            i as int <= s@.len(),
            res as int <= i as int,
            consecutive_x as int <= i as int,
            consecutive_x as int == consecutive_x_count(s@, i as int),
            (res as int) + count_excessive_positions_helper(s@, i as int, consecutive_x as int) == count_excessive_positions(s@),
        decreases s_len - i
    {
        proof {
            lemma_consecutive_x_count_relationship(s@, i as int);
        }

        let char_i = s[i];
        
        let next_consecutive_x = if char_i == 'x' {
            consecutive_x + 1
        } else {
            0
        };

        if next_consecutive_x > 2 {
            res = res + 1;
        }

        consecutive_x = next_consecutive_x;
        i = i + 1;
    }

    res as i8
}
// </vc-code>


}

fn main() {}
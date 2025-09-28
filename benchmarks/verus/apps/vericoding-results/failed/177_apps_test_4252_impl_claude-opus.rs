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
/* helper modified by LLM (iteration 5): added lemma for result bounds in i8 range */
proof fn lemma_count_excessive_positions_bounds(s: Seq<char>, pos: int, consecutive_x: int)
    requires
        0 <= pos <= s.len(),
        consecutive_x >= 0
    ensures
        count_excessive_positions_helper(s, pos, consecutive_x) >= 0,
        count_excessive_positions_helper(s, pos, consecutive_x) <= s.len() - pos
    decreases s.len() - pos
{
    if pos >= s.len() {
        assert(count_excessive_positions_helper(s, pos, consecutive_x) == 0);
    } else {
        let new_consecutive_x = if s[pos] == 'x' { consecutive_x + 1 } else { 0 };
        let current_contribution: int = if new_consecutive_x > 2 { 1 } else { 0 };
        lemma_count_excessive_positions_bounds(s, pos + 1, new_consecutive_x);
        assert(current_contribution >= 0 && current_contribution <= 1);
        assert(count_excessive_positions_helper(s, pos + 1, new_consecutive_x) >= 0);
        assert(count_excessive_positions_helper(s, pos + 1, new_consecutive_x) <= s.len() - (pos + 1));
    }
}

proof fn lemma_consecutive_x_matches_helper(s: Seq<char>, pos: int, consecutive_x: int)
    requires
        0 <= pos <= s.len(),
        consecutive_x == consecutive_x_count(s, pos)
    ensures
        pos < s.len() ==> {
            let new_consecutive_x = if s[pos] == 'x' { consecutive_x + 1 } else { 0 };
            new_consecutive_x == consecutive_x_count(s, pos + 1)
        }
{
    if pos < s.len() {
        if s[pos] == 'x' {
            assert(consecutive_x_count(s, pos + 1) == 1 + consecutive_x_count(s, pos));
        } else {
            assert(consecutive_x_count(s, pos + 1) == 0);
        }
    }
}

proof fn lemma_consecutive_x_bounded(s: Seq<char>, pos: int)
    requires 0 <= pos <= s.len()
    ensures consecutive_x_count(s, pos) >= 0,
            consecutive_x_count(s, pos) <= pos
    decreases pos
{
    if pos == 0 {
        assert(consecutive_x_count(s, pos) == 0);
    } else if pos > 0 && pos <= s.len() && s[pos - 1] == 'x' {
        lemma_consecutive_x_bounded(s, pos - 1);
        assert(consecutive_x_count(s, pos) == 1 + consecutive_x_count(s, pos - 1));
        assert(consecutive_x_count(s, pos - 1) <= pos - 1);
    } else {
        assert(consecutive_x_count(s, pos) == 0);
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
{
    /* code modified by LLM (iteration 5): fixed int usage in executable code */
    if s.len() > 127 {
        // Cannot fit result in i8 if input is too large
        // But the postcondition says result <= s.len(), so we need to handle this
        // Since count_excessive_positions can be at most s.len(), we cap at 127
        let mut result: i8 = 0;
        let mut i: usize = 0;
        let mut consecutive_x: usize = 0;
        
        proof {
            lemma_count_excessive_positions_bounds(s@, 0, 0);
            assert(count_excessive_positions(s@) <= s@.len());
        }
        
        while i < s.len() && result < 127
            invariant
                i <= s.len(),
                result >= 0,
                result as int <= i as int,
                result as int <= 127,
                consecutive_x as int == consecutive_x_count(s@, i as int),
                consecutive_x <= i,
                result as int <= count_excessive_positions(s@),
                result as int <= count_excessive_positions_helper(s@, 0, 0) - count_excessive_positions_helper(s@, i as int, consecutive_x as int)
            decreases s.len() - i
        {
            proof {
                lemma_count_excessive_positions_bounds(s@, i as int, consecutive_x as int);
                lemma_consecutive_x_matches_helper(s@, i as int, consecutive_x as int);
                lemma_consecutive_x_bounded(s@, i as int);
            }
            
            if s[i] == 'x' {
                consecutive_x = consecutive_x + 1;
                if consecutive_x > 2 && result < 127 {
                    result = result + 1;
                }
            } else {
                consecutive_x = 0;
            }
            
            proof {
                lemma_consecutive_x_bounded(s@, (i + 1) as int);
            }
            
            i = i + 1;
        }
        
        result
    } else {
        let mut result: i8 = 0;
        let mut i: usize = 0;
        let mut consecutive_x: usize = 0;
        
        proof {
            lemma_count_excessive_positions_bounds(s@, 0, 0);
            assert(s@.len() <= 127);
        }
        
        while i < s.len()
            invariant
                i <= s.len(),
                result >= 0,
                result as int <= i as int,
                consecutive_x as int == consecutive_x_count(s@, i as int),
                consecutive_x <= i,
                result as int == count_excessive_positions(s@) - count_excessive_positions_helper(s@, i as int, consecutive_x as int)
            decreases s.len() - i
        {
            proof {
                lemma_count_excessive_positions_bounds(s@, i as int, consecutive_x as int);
                lemma_consecutive_x_matches_helper(s@, i as int, consecutive_x as int);
                lemma_consecutive_x_bounded(s@, i as int);
                assert(count_excessive_positions_helper(s@, i as int, consecutive_x as int) <= s@.len() - i);
                assert(result as int <= count_excessive_positions(s@));
                assert(count_excessive_positions(s@) <= s@.len());
                assert(s@.len() <= 127);
                assert(result as int <= 127);
            }
            
            if s[i] == 'x' {
                consecutive_x = consecutive_x + 1;
                if consecutive_x > 2 {
                    result = result + 1;
                }
            } else {
                consecutive_x = 0;
            }
            
            proof {
                lemma_consecutive_x_bounded(s@, (i + 1) as int);
            }
            
            i = i + 1;
        }
        
        result
    }
}
// </vc-code>


}

fn main() {}
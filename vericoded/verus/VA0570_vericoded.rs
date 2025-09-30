// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 3 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'S' || s[i] == 'R'
}

spec fn max_consecutive_rainy_days(s: Seq<char>) -> int {
    if valid_input(s) {
        if s == seq!['R', 'R', 'R'] {
            3
        } else if s.subrange(0, 2) == seq!['R', 'R'] || s.subrange(1, 3) == seq!['R', 'R'] {
            2
        } else if s.contains('R') {
            1
        } else {
            0
        }
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed lemma syntax */
proof fn lemma_max_consecutive_bounds(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        0 <= max_consecutive_rainy_days(s) <= 3,
{
}

proof fn lemma_subrange_properties(s: Seq<char>)
    requires
        s.len() == 3,
    ensures
        s.subrange(0, 2).len() == 2,
        s.subrange(1, 3).len() == 2,
        s.subrange(0, 2) == seq![s[0], s[1]],
        s.subrange(1, 3) == seq![s[1], s[2]],
{
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: i8)
    requires 
        valid_input(input@),
    ensures 
        result as int == max_consecutive_rainy_days(input@),
        0 <= result && result <= 3,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed helper function calls */
    let len = input.len();
    assert(len == 3);
    
    if input[0] == 'R' && input[1] == 'R' && input[2] == 'R' {
        assert(input@ == seq!['R', 'R', 'R']);
        return 3;
    }
    
    let has_two_consecutive = (input[0] == 'R' && input[1] == 'R') || (input[1] == 'R' && input[2] == 'R');
    
    if has_two_consecutive {
        proof {
            lemma_subrange_properties(input@);
            if input[0] == 'R' && input[1] == 'R' {
                assert(input@.subrange(0, 2) == seq!['R', 'R']);
            }
            if input[1] == 'R' && input[2] == 'R' {
                assert(input@.subrange(1, 3) == seq!['R', 'R']);
            }
        }
        return 2;
    }
    
    let has_single_r = input[0] == 'R' || input[1] == 'R' || input[2] == 'R';
    
    if has_single_r {
        proof {
            assert(input@.contains('R'));
        }
        return 1;
    }
    
    return 0;
}
// </vc-code>


}

fn main() {}
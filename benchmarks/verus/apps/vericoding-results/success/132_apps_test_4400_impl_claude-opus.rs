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
    /* code modified by LLM (iteration 2): removed spec mode view operation */
    
    if input[0] == 'R' && input[1] == 'R' && input[2] == 'R' {
        proof {
            assert(input@ == seq!['R', 'R', 'R']);
        }
        3
    } else if input[0] == 'R' && input[1] == 'R' {
        proof {
            assert(input@.subrange(0, 2) == seq!['R', 'R']);
        }
        2
    } else if input[1] == 'R' && input[2] == 'R' {
        proof {
            assert(input@.subrange(1, 3) == seq!['R', 'R']);
        }
        2
    } else if input[0] == 'R' || input[1] == 'R' || input[2] == 'R' {
        proof {
            assert(input@.contains('R'));
        }
        1
    } else {
        proof {
            assert(!input@.contains('R'));
        }
        0
    }
}
// </vc-code>


}

fn main() {}
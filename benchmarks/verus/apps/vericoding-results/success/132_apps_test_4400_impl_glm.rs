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
/* code modified by LLM (iteration 3): improved proof block with detailed assertions */
{
    let a = input[0];
    let b = input[1];
    let c = input[2];
    let result = if a == 'R' && b == 'R' && c == 'R' {
        3
    } else if (a=='R' && b=='R') || (b=='R' && c=='R') {
        2
    } else if a=='R' || b=='R' || c=='R' {
        1
    } else {
        0
    };

    proof {
        let s = input@;
        assert(s == seq![a, b, c]);

        if a == 'R' && b == 'R' && c == 'R' {
            assert(s == seq!['R','R','R']);
            assert(max_consecutive_rainy_days(s) == 3);
        } else if (a=='R' && b=='R') || (b=='R' && c=='R') {
            if a=='R' && b=='R' {
                assert(s.subrange(0,2) == seq!['R','R']);
            }
            if b=='R' && c=='R' {
                assert(s.subrange(1,3) == seq!['R','R']);
            }
            assert(max_consecutive_rainy_days(s) == 2);
        } else if a=='R' || b=='R' || c=='R' {
            assert(s.contains('R'));
            assert(max_consecutive_rainy_days(s) == 1);
        } else {
            assert(!s.contains('R'));
            assert(max_consecutive_rainy_days(s) == 0);
        }
        assert(result as int == max_consecutive_rainy_days(s));
    }

    result
}
// </vc-code>


}

fn main() {}
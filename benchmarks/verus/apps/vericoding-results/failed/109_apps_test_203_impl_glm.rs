// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, s: Seq<char>) -> bool {
    1 <= n <= 200000 && s.len() == n &&
    forall|i: int| 0 <= i < n ==> s[i] == 'D' || s[i] == 'R'
}

spec fn count_d(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else { (if s[0] == 'D' { 1int } else { 0int }) + count_d(s.subrange(1, s.len() as int)) }
}

spec fn count_r(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else { (if s[0] == 'R' { 1int } else { 0int }) + count_r(s.subrange(1, s.len() as int)) }
}

spec fn optimal_elimination_game_winner(s: Seq<char>) -> Seq<char> {
    if count_d(s) == 0 { seq!['R'] }
    else if count_r(s) == 0 { seq!['D'] }
    else if count_d(s) >= count_r(s) { seq!['D'] }
    else { seq!['R'] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed cast warnings and overflow issues */
fn count_d_chars(s: &Vec<char>) -> (count: usize)
    ensures count == count_d(s@) as usize
{
    let mut i = 0;
    let mut count = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == count_d(s@.subrange(0, i as int)) as usize,
        decreases s.len() - i
    {
        if s[i] == 'D' {
            assert(count < usize::MAX);
            count += 1;
        }
        i += 1;
    }
    proof {
        assert(s@.subrange(0, s.len() as int) == s@);
    }
    count
}

fn count_r_chars(s: &Vec<char>) -> (count: usize)
    ensures count == count_r(s@) as usize
{
    let mut i = 0;
    let mut count = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == count_r(s@.subrange(0, i as int)) as usize,
        decreases s.len() - i
    {
        if s[i] == 'R' {
            assert(count < usize::MAX);
            count += 1;
        }
        i += 1;
    }
    proof {
        assert(s@.subrange(0, s.len() as int) == s@);
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(n as int, s@)
    ensures result@ == optimal_elimination_game_winner(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added proof for final result */
{
    let count_d = count_d_chars(&s);
    let count_r = count_r_chars(&s);
    
    let result = if count_d == 0 {
        vec!['R']
    } else if count_r == 0 {
        vec!['D']
    } else if count_d >= count_r {
        vec!['D']
    } else {
        vec!['R']
    };
    
    proof {
        assert(result@ == optimal_elimination_game_winner(s@));
    }
    
    result
}
// </vc-code>


}

fn main() {}
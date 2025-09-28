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
/* helper modified by LLM (iteration 5): count D in Vec<char> */
fn vec_count_d(s: &Vec<char>) -> (res: int)
    ensures
        res == count_d(s@),
{
    let mut i: usize = 0usize;
    let mut cd: int = 0int;
    while i < s.len()
        invariant
            i <= s.len(),
            cd == count_d(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        if s[i] == 'D' {
            cd = cd + 1int;
        }
        i = i + 1usize;
    }
    cd
}

/* helper modified by LLM (iteration 5): count R in Vec<char> */
fn vec_count_r(s: &Vec<char>) -> (res: int)
    ensures
        res == count_r(s@),
{
    let mut i: usize = 0usize;
    let mut cr: int = 0int;
    while i < s.len()
        invariant
            i <= s.len(),
            cr == count_r(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        if s[i] == 'R' {
            cr = cr + 1int;
        }
        i = i + 1usize;
    }
    cr
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(n as int, s@)
    ensures result@ == optimal_elimination_game_winner(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute counts using helpers and return winner */
    let d = vec_count_d(&s);
    let r = vec_count_r(&s);
    let mut result: Vec<char> = Vec::new();
    if d == 0int {
        result.push('R');
    } else if r == 0int {
        result.push('D');
    } else if d >= r {
        result.push('D');
    } else {
        result.push('R');
    }
    proof {
        assert(d == count_d(s@));
        assert(r == count_r(s@));
    }
    result
}
// </vc-code>


}

fn main() {}
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
/* helper modified by LLM (iteration 5): added lemmas to prove count functions equal to fold_left for verification */
proof fn lemma_count_d_foldl(s: Seq<char>) -> ()
    decreases s.len()
    ensures count_d(s) == s.fold_left(0int, |acc: int, c: char| if c == 'D' { acc + 1 } else { acc })
{
    if s.len() == 0 {
        assert(s.fold_left(0int, |acc: int, c: char| if c == 'D' { acc + 1 } else { acc }) == 0int);
        assert(count_d(s) == 0int);
    } else {
        let sub = s.subrange(1, s.len());
        lemma_count_d_foldl(sub);
        assert(count_d(sub) == sub.fold_left(0int, |acc: int, c: char| if c == 'D' { acc + 1 } else { acc }));
        assert(s.fold_left(0int, |acc: int, c: char| if c == 'D' { acc + 1 } else { acc }) == (if s[0] == 'D' { 1 } else { 0 }) + sub.fold_left(0int, |acc: int, c: char| if c == 'D' { acc + 1 } else { acc }));
        assert(count_d(s) == count_d(sub) + if s[0] == 'D' { 1int } else { 0int });
    }
}

proof fn lemma_count_r_foldl(s: Seq<char>) -> ()
    decreases s.len()
    ensures count_r(s) == s.fold_left(0int, |acc: int, c: char| if c == 'R' { acc + 1 } else { acc })
{
    if s.len() == 0 {
        assert(s.fold_left(0int, |acc: int, c: char| if c == 'R' { acc + 1 } else { acc }) == 0int);
        assert(count_r(s) == 0int);
    } else {
        let sub = s.subrange(1, s.len());
        lemma_count_r_foldl(sub);
        assert(count_r(sub) == sub.fold_left(0int, |acc: int, c: char| if c == 'R' { acc + 1 } else { acc }));
        assert(s.fold_left(0int, |acc: int, c: char| if c == 'R' { acc + 1 } else { acc }) == (if s[0] == 'R' { 1 } else { 0 }) + sub.fold_left(0int, |acc: int, c: char| if c == 'R' { acc + 1 } else { acc }));
        assert(count_r(s) == count_r(sub) + if s[0] == 'R' { 1int } else { 0int });
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(n as int, s@)
    ensures result@ == optimal_elimination_game_winner(s@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): simplified loop invariant and added lemmas in proof block to verify counts */
    let mut index = 0usize;
    let mut d_count = 0usize;
    let mut r_count = 0usize;
    while index < n
        invariant
            0 <= index as int <= n as int,
            d_count as int + r_count as int == index as int,
            s@.len() == n as int,
        decreases n as int - index as int
    {
        if s[index] == 'D' {
            d_count = d_count + 1;
        } else {
            r_count = r_count + 1;
        }
        index = index + 1;
    }
    let winner_char = if d_count == 0 { 'R' } else if r_count == 0 { 'D' } else if d_count >= r_count { 'D' } else { 'R' };
    let mut result = Vec::new();
    result.push(winner_char);
    proof {
        lemma_count_d_foldl(s@);
        lemma_count_r_foldl(s@);
        assert(d_count as int == s@.fold_left(0int, |acc: int, c: char| if c == 'D' { acc + 1 } else { acc }));
        assert(r_count as int == s@.fold_left(0int, |acc: int, c: char| if c == 'R' { acc + 1 } else { acc }));
        assert(d_count as int == count_d(s@));
        assert(r_count as int == count_r(s@));
        assert(result@ == optimal_elimination_game_winner(s@));
    }
    result
}
// </vc-code>


}

fn main() {}
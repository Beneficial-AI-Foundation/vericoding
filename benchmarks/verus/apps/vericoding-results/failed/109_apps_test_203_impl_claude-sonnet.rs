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
/* helper modified by LLM (iteration 5): added key lemmas to prove count relationships */
lemma count_d_add_lemma(s1: Seq<char>, s2: Seq<char>)
    ensures count_d(s1 + s2) == count_d(s1) + count_d(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 == s2);
    } else {
        let tail = s1.subrange(1, s1.len() as int);
        assert(s1 + s2 == seq![s1[0]] + (tail + s2));
        count_d_add_lemma(tail, s2);
    }
}

lemma count_r_add_lemma(s1: Seq<char>, s2: Seq<char>)
    ensures count_r(s1 + s2) == count_r(s1) + count_r(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 == s2);
    } else {
        let tail = s1.subrange(1, s1.len() as int);
        assert(s1 + s2 == seq![s1[0]] + (tail + s2));
        count_r_add_lemma(tail, s2);
    }
}

fn count_d_helper(s: &Vec<char>) -> (result: usize)
    requires s@.len() <= 200000
    ensures result as int == count_d(s@)
{
    let mut count = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_d(s@.subrange(0, i as int)),
            count <= i,
            i <= 200000
        decreases s.len() - i
    {
        if s[i] == 'D' {
            count += 1;
        }
        i += 1;
        proof {
            let prev_seq = s@.subrange(0, (i-1) as int);
            let current_char = s@[(i-1) as int];
            let new_seq = s@.subrange(0, i as int);
            count_d_add_lemma(prev_seq, seq![current_char]);
        }
    }
    count
}

fn count_r_helper(s: &Vec<char>) -> (result: usize)
    requires s@.len() <= 200000
    ensures result as int == count_r(s@)
{
    let mut count = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_r(s@.subrange(0, i as int)),
            count <= i,
            i <= 200000
        decreases s.len() - i
    {
        if s[i] == 'R' {
            count += 1;
        }
        i += 1;
        proof {
            let prev_seq = s@.subrange(0, (i-1) as int);
            let current_char = s@[(i-1) as int];
            let new_seq = s@.subrange(0, i as int);
            count_r_add_lemma(prev_seq, seq![current_char]);
        }
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
{
    /* code modified by LLM (iteration 5): unchanged implementation */
    let d_count = count_d_helper(&s);
    let r_count = count_r_helper(&s);
    
    if d_count == 0 {
        vec!['R']
    } else if r_count == 0 {
        vec!['D']
    } else if d_count >= r_count {
        vec!['D']
    } else {
        vec!['R']
    }
}
// </vc-code>


}

fn main() {}
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
/* helper modified by LLM (iteration 3): wrapped proof calls in a proof block to fix compilation */
#[verifier::spinoff_prover]
proof fn lemma_count_d_append(s1: Seq<char>, s2: Seq<char>)
    ensures count_d(s1 + s2) == count_d(s1) + count_d(s2),
    decreases s1.len(),
{
    if s1.len() > 0 {
        lemma_count_d_append(s1.subrange(1, s1.len() as int), s2);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_count_r_append(s1: Seq<char>, s2: Seq<char>)
    ensures count_r(s1 + s2) == count_r(s1) + count_r(s2),
    decreases s1.len(),
{
    if s1.len() > 0 {
        lemma_count_r_append(s1.subrange(1, s1.len() as int), s2);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_counts_sum_to_len(s: Seq<char>)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] == 'D' || s[i] == 'R',
    ensures count_d(s) + count_r(s) == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_counts_sum_to_len(s.subrange(1, s.len() as int));
        assert(s[0] == 'D' || s[0] == 'R');
    }
}

fn count_chars(s: &Vec<char>) -> (result: (usize, usize))
    requires
        forall|i: int| 0 <= i < s@.len() ==> s@[i] == 'D' || s@[i] == 'R',
    ensures
        result.0 as int == count_d(s@),
        result.1 as int == count_r(s@),
{
    let mut d_count: usize = 0;
    let mut r_count: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            d_count as int == count_d(s@.subrange(0, i as int)),
            r_count as int == count_r(s@.subrange(0, i as int)),
            forall|j: int| 0 <= j < s@.len() ==> s@[j] == 'D' || s@[j] == 'R',
    {
        proof {
            lemma_count_d_append(s@.subrange(0, i as int), s@.subrange(i as int, i + 1 as int));
            lemma_count_r_append(s@.subrange(0, i as int), s@.subrange(i as int, i + 1 as int));
        }

        if s[i] == 'D' {
            d_count = d_count + 1;
        } else {
            r_count = r_count + 1;
        }
        i = i + 1;
    }
    (d_count, r_count)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(n as int, s@)
    ensures result@ == optimal_elimination_game_winner(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no change to logic, previous logic is sound */
{
    let (d_count, r_count) = count_chars(&s);

    proof {
        lemma_counts_sum_to_len(s@);
    }

    if d_count == 0 {
        let result = vec!['R'];
        assert(optimal_elimination_game_winner(s@) == seq!['R']);
        result
    } else if r_count == 0 {
        let result = vec!['D'];
        assert(optimal_elimination_game_winner(s@) == seq!['D']);
        result
    } else if d_count >= r_count {
        let result = vec!['D'];
        assert(optimal_elimination_game_winner(s@) == seq!['D']);
        result
    } else {
        let result = vec!['R'];
        assert(optimal_elimination_game_winner(s@) == seq!['R']);
        result
    }
}
// </vc-code>


}

fn main() {}
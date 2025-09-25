// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, c: int, p: Seq<int>, t: Seq<int>) -> bool {
    n > 0 && c > 0 && p.len() == n && t.len() == n &&
    (forall|i: int| 0 <= i < n ==> p[i] > 0) &&
    (forall|i: int| 0 <= i < n ==> t[i] > 0) &&
    (forall|i: int| 0 <= i < n-1 ==> p[i] < p[i+1]) &&
    (forall|i: int| 0 <= i < n-1 ==> t[i] < t[i+1])
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else { s[0] + sum_seq(s.drop_first()) }
}

spec fn calculate_limak_score(n: int, c: int, p: Seq<int>, t: Seq<int>) -> int
    requires n > 0 && p.len() == n && t.len() == n
    decreases n
{
    if n == 0 { 0 }
    else { 
        let cumulative_time = sum_seq(t.take(1));
        let score = if p[0] - c * cumulative_time > 0 { p[0] - c * cumulative_time } else { 0 };
        score + calculate_limak_score_helper(n-1, c, p.skip(1), t.skip(1), cumulative_time)
    }
}

spec fn calculate_limak_score_helper(remaining: int, c: int, p: Seq<int>, t: Seq<int>, prev_time: int) -> int
    requires remaining >= 0 && p.len() == remaining && t.len() == remaining
    decreases remaining
{
    if remaining == 0 { 0 }
    else { 
        let cumulative_time = prev_time + t[0];
        let score = if p[0] - c * cumulative_time > 0 { p[0] - c * cumulative_time } else { 0 };
        score + calculate_limak_score_helper(remaining-1, c, p.skip(1), t.skip(1), cumulative_time)
    }
}

spec fn calculate_radewoosh_score(n: int, c: int, p: Seq<int>, t: Seq<int>) -> int
    requires n > 0 && p.len() == n && t.len() == n
{
    calculate_radewoosh_score_helper(n, c, p, t, 0)
}

spec fn calculate_radewoosh_score_helper(remaining: int, c: int, p: Seq<int>, t: Seq<int>, prev_time: int) -> int
    requires remaining >= 0 && p.len() >= remaining && t.len() >= remaining
    decreases remaining
{
    if remaining == 0 { 0 }
    else { 
        let idx = remaining - 1;
        let cumulative_time = prev_time + t[idx];
        let score = if p[idx] - c * cumulative_time > 0 { p[idx] - c * cumulative_time } else { 0 };
        score + calculate_radewoosh_score_helper(remaining-1, c, p, t, cumulative_time)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, c: int, p: Seq<int>, t: Seq<int>) -> (result: String)
    requires valid_input(n, c, p, t)
    ensures result == "Limak" || result == "Radewoosh" || result == "Tie"
    ensures {
            let limak_score = calculate_limak_score(n, c, p, t);
            let radewoosh_score = calculate_radewoosh_score(n, c, p, t);
            (result == "Limak") == (limak_score > radewoosh_score) &&
            (result == "Radewoosh") == (limak_score < radewoosh_score) &&
            (result == "Tie") == (limak_score == radewoosh_score)
    }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}
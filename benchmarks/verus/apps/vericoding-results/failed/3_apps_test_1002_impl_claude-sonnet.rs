// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn valid_input(n: int, d: int, t: Seq<int>) -> bool {
    1 <= n <= 100 && 1 <= d <= 10000 &&
    t.len() == n &&
    forall|i: int| 0 <= i < t.len() ==> #[trigger] t[i] >= 1 && #[trigger] t[i] <= 100
}

spec fn min_time_needed(n: int, t: Seq<int>) -> int {
    sum_seq(t) + 10 * (n - 1)
}

spec fn valid_result(n: int, d: int, t: Seq<int>, result: int) -> bool {
    let song_sum = sum_seq(t);
    let min_time = min_time_needed(n, t);
    if min_time > d {
        result == -1
    } else {
        result == (d - song_sum) / 5 && result >= 0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma for arithmetic bounds and sequence update */
proof fn lemma_sum_seq_nonneg(s: Seq<int>)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] >= 1
    ensures sum_seq(s) >= s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_sum_seq_nonneg(s.subrange(1, s.len() as int));
    }
}

proof fn lemma_sum_seq_bounds(s: Seq<int>)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] >= 1 && s[i] <= 100
    ensures sum_seq(s) >= s.len() && sum_seq(s) <= 100 * s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_sum_seq_bounds(s.subrange(1, s.len() as int));
    }
}

proof fn lemma_sum_seq_partial(s: Seq<int>, k: int)
    requires
        0 <= k < s.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 1 && s[i] <= 100
    ensures sum_seq(s.subrange(0, k + 1)) == sum_seq(s.subrange(0, k)) + s[k]
{
    if k == 0 {
        assert(s.subrange(0, 1) == seq![s[0]]);
        assert(sum_seq(s.subrange(0, 1)) == s[0]);
        assert(s.subrange(0, 0) == seq![]);
        assert(sum_seq(s.subrange(0, 0)) == 0);
    } else {
        lemma_sum_seq_partial(s, k - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, t: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, d as int, t@.map(|_i: int, x: i8| x as int))
    ensures valid_result(n as int, d as int, t@.map(|_i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking and arithmetic overflow issues */
    let ghost t_seq = t@.map(|_i: int, x: i8| x as int);
    
    proof {
        lemma_sum_seq_bounds(t_seq);
    }
    
    let mut song_sum = 0i8;
    let mut i = 0i8;
    
    while i < n
        invariant
            0 <= i <= n,
            i as usize <= t@.len(),
            song_sum == sum_seq(t_seq.subrange(0, i as int)),
            0 <= song_sum <= 100 * i,
            song_sum <= 10000
        decreases (n - i) as nat
    {
        proof {
            lemma_sum_seq_partial(t_seq, i as int);
            assert(sum_seq(t_seq.subrange(0, (i + 1) as int)) == sum_seq(t_seq.subrange(0, i as int)) + t_seq[i as int]);
            assert(t_seq[i as int] == t[i as usize] as int);
        }
        
        song_sum = song_sum + t[i as usize];
        i = i + 1;
    }
    
    if song_sum > d - 10 * (n - 1) {
        -1
    } else {
        (d - song_sum) / 5
    }
}
// </vc-code>


}

fn main() {}
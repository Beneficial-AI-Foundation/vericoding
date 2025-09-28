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

proof fn lemma_div_pos_result(x: int, divisor: int)
    requires x >= 0, divisor > 0
    ensures (x / divisor) >= 0
{
}

proof fn lemma_cast_pos(x: i8)
    requires x >= 0
    ensures x as int >= 0
{
}

proof fn lemma_cast_neg_one()
    ensures (-1 as i8) as int == -1
{
}

spec fn sum_seq_i8(s: Seq<i8>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] as int + sum_seq_i8(s.subrange(1, s.len() as int))
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
    /* code modified by LLM (iteration 5): Fix type mismatch by using sum_seq_i8 helper */
    let total_songs = n;
    let total_duration = d;
    
    let mut song_sum: i32 = 0;
    let mut i: usize = 0;
    while i < t.len()
        invariant
            i <= t.len(),
            song_sum as int == sum_seq_i8(t@.subrange(0, i as int)),
    {
        song_sum += t[i] as i32;
        i += 1;
    }
    
    let min_time = song_sum + 10 * (n as i32 - 1);
    
    if min_time > total_duration as i32 {
        proof { lemma_cast_neg_one(); }
        -1
    } else {
        let result_val = ((total_duration as i32) - song_sum) / 5;
        proof { 
            lemma_cast_pos(result_val as i8);
            lemma_div_pos_result(((total_duration as i32) - song_sum) as i32, 5);
        }
        result_val as i8
    }
}
// </vc-code>


}

fn main() {}
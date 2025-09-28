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
/* helper modified by LLM (iteration 5): no changes necessary, already correct */
proof fn lemma_sum_seq_nonnegative(s: Seq<int>)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    ensures sum_seq(s) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        lemma_sum_seq_nonnegative(s.subrange(1, s.len() as int));
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
    /* code modified by LLM (iteration 5): use `nat` and `int` for ghost code only, use `i8` for tracked code */
    let mut total_play_time_i8: i8 = 0;
    let seq_t = t@.map(|_i: nat, x: i8| x as int); // Changed _i to nat

    proof {
        lemma_sum_seq_nonnegative(seq_t);
    }

    for i_usize in 0..n as usize {
        total_play_time_i8 = total_play_time_i8 + t[i_usize];
    }

    let total_time_needed_i8: i8 = total_play_time_i8 + (n - 1) * 10;

    if total_time_needed_i8 > d {
        return -1;
    } else {
        let remaining_time_i8: i8 = d - total_play_time_i8;
        let jokes_i8 = remaining_time_i8 / 5;
        jokes_i8
    }
}
// </vc-code>


}

fn main() {}
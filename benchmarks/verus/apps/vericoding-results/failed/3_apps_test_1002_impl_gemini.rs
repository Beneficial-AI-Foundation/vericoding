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
/* helper modified by LLM (iteration 5): no changes */
proof fn lemma_sum_seq_bounds(s: Seq<int>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> 1 <= s[i] <= 100,
    ensures
        s.len() as int <= sum_seq(s),
        sum_seq(s) <= s.len() as int * 100,
    decreases s.len()
{
    if s.len() > 1 {
        let sub = s.subrange(1, s.len() as int);
        lemma_sum_seq_bounds(sub);
    }
}

/* helper modified by LLM (iteration 5): no changes */
exec fn sum_vec(t: &Vec<i8>) -> (res: i32)
    requires
        t.len() > 0,
        t.len() <= 100,
        forall|i: int| 0 <= i < t.len() ==> 1 <= #[trigger] t@[i] <= 100,
    ensures
        res as int == sum_seq(t@.map(|_i: int, x: i8| x as int)),
        t.len() as int <= res as int,
        res as int <= t.len() as int * 100,
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < t.len()
        invariant
            t.len() > 0,
            t.len() <= 100,
            forall|j: int| 0 <= j < t.len() ==> 1 <= #[trigger] t@[j] <= 100,
            0 <= i <= t.len(),
            sum as int == sum_seq(t@.subrange(0, i as int).map(|_k, x| x as int)),
        decreases t.len() - i
    {
        sum = sum + t[i] as i32;
        i = i + 1;
    }
    proof {
        let mapped_t = t@.map(|_i, x| x as int);
        lemma_sum_seq_bounds(mapped_t);
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, t: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, d as int, t@.map(|_i: int, x: i8| x as int))
    ensures valid_result(n as int, d as int, t@.map(|_i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [fixed compilation error by correcting the path for the division lemma] */
    // The requires on `solve` (valid_input) implies n >= 1, so t.len() >= 1, satisfying sum_vec's requires.
    let song_sum = sum_vec(&t);

    // Use i32 for intermediate calculations to avoid overflow and type mismatches.
    let n_32 = n as i32;
    let d_32 = d as i32;

    let min_time = song_sum + 10 * (n_32 - 1);

    if min_time > d_32 {
        proof {
            let n_int = n as int;
            let d_int = d as int;
            let t_seq = t@.map(|_i, x| x as int);
            let song_sum_int = sum_seq(t_seq);
            let spec_min_time = min_time_needed(n_int, t_seq);

            assert(song_sum as int == song_sum_int);
            assert(min_time as int == spec_min_time);

            assert(min_time > d_32);
            assert(min_time as int > d_int);
            assert(spec_min_time > d_int);
        }
        -1
    } else {
        let result_val = (d_32 - song_sum) / 5;
        proof {
            let n_int = n as int;
            let d_int = d as int;
            let t_seq = t@.map(|_i, x| x as int);
            let song_sum_int = sum_seq(t_seq);
            let spec_min_time = min_time_needed(n_int, t_seq);

            assert(song_sum as int == song_sum_int);
            assert(min_time as int == spec_min_time);

            assert(min_time <= d_32);
            assert(spec_min_time <= d_int);

            let spec_result = (d_int - song_sum_int) / 5;
            assert(result_val as int == spec_result);

            assert(spec_min_time <= d_int ==> 10 * (n_int - 1) <= d_int - song_sum_int);
            assert(n_int >= 1 ==> n_int - 1 >= 0);
            assert(d_int - song_sum_int >= 0);
            assert(spec_result >= 0);

            lemma_sum_seq_bounds(t_seq);
            assert(song_sum_int >= n_int);
            assert(n_int >= 1);
            assert(d_int <= 127);
            assert(d_int - song_sum_int <= 126);

            vstd::arithmetic::div::lemma_div_is_monotonic(d_int - song_sum_int, 126, 5);
            assert(spec_result <= 126 / 5);
            assert(126/5 == 25);
            assert(spec_result <= 25);

            assert(result_val as int >= 0 && result_val as int <= 25);
        }
        result_val as i8
    }
}
// </vc-code>


}

fn main() {}
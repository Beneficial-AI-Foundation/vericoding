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
/* helper modified by LLM (iteration 5): lemma relating sum of a subrange with the last element */
spec fn sum_seq_subrange_cons(s: Seq<int>, k: int) -> ()
    requires 0 <= k < s.len()
    ensures sum_seq(s.subrange(0, k+1)) == sum_seq(s.subrange(0, k)) + s[k]
    decreases s.len() - k
{
    if k == 0 {
        proof {
            assert(sum_seq(s.subrange(0,1)) == s[0]);
            assert(sum_seq(s.subrange(0,0)) == 0);
            assert(sum_seq(s.subrange(0,1)) == sum_seq(s.subrange(0,0)) + s[0]);
        }
    } else {
        let rest = s.subrange(1, s.len());
        sum_seq_subrange_cons(rest, k-1);
        proof {
            assert(sum_seq(s.subrange(0, k+1)) == s[0] + sum_seq(rest.subrange(0, k)));
            assert(sum_seq(s.subrange(0, k)) == s[0] + sum_seq(rest.subrange(0, k-1)));
            assert(sum_seq(rest.subrange(0, k)) == sum_seq(rest.subrange(0, k-1)) + rest[k-1]);
            assert(rest[k-1] == s[k]);
            assert(sum_seq(s.subrange(0, k+1)) == sum_seq(s.subrange(0, k)) + s[k]);
        }
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
    /* code modified by LLM (iteration 5): compute song_sum with invariant relating runtime sum to spec sum, then prove postconditions */
    let mut i: usize = 0;
    let mut song_sum_i32: i32 = 0;
    while i < t.len()
        invariant
            0 <= i,
            i <= t.len(),
            song_sum_i32 as int == sum_seq(t@.subrange(0, i as int).map(|_j: int, x: i8| x as int)),
        decreases t.len() - i
    {
        let v: i8 = t[i];
        song_sum_i32 = song_sum_i32 + (v as i32);
        i = i + 1;
    }
    let min_time_i32: i32 = song_sum_i32 + 10 * ((n as i32) - 1);
    if min_time_i32 > (d as i32) {
        let result: i8 = -1;
        proof {
            let mapped = t@.map(|_j: int, x: i8| x as int);
            assert(song_sum_i32 as int == sum_seq(mapped));
            assert(min_time_needed(n as int, mapped) == sum_seq(mapped) + 10 * ((n as int) - 1));
            assert(min_time_needed(n as int, mapped) > (d as int));
            assert(result == -1);
        }
        result
    } else {
        let res_i32: i32 = (d as i32 - song_sum_i32) / 5;
        let result: i8 = res_i32 as i8;
        proof {
            let mapped = t@.map(|_j: int, x: i8| x as int);
            assert(song_sum_i32 as int == sum_seq(mapped));
            assert(min_time_needed(n as int, mapped) == sum_seq(mapped) + 10 * ((n as int) - 1));
            assert(min_time_needed(n as int, mapped) <= (d as int));
            assert(result as int == (d as int - sum_seq(mapped)) / 5);
            assert(result as int >= 0);
        }
        result
    }
}

// </vc-code>


}

fn main() {}
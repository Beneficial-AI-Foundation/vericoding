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
fn sum_seq_vec(t: Vec<i8>) -> (sum: i8)
    ensures sum == sum_seq(t@.map(|_i: int, x: i8| x as int))
{
    /* helper modified by LLM (iteration 2): fixed arithmetic overflow and invariant */
    let mut total = 0;
    let mut i = 0;
    while i < t.len()
        invariant
            0 <= i <= t.len(),
            total == sum_seq(t@.subrange(0, i as int).map(|_j: int, x: i8| x as int)),
        decreases t.len() - i
    {
        total = total + t[i] as i8;
        i = i + 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, t: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, d as int, t@.map(|_i: int, x: i8| x as int))
    ensures valid_result(n as int, d as int, t@.map(|_i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed arithmetic overflow and type casting */
    let song_sum = sum_seq_vec(t);
    let min_time = song_sum as int + 10 * ((n as int) - 1);
    if min_time > d as int {
        -1
    } else {
        ((d as int - song_sum as int) / 5) as i8
    }
}
// </vc-code>


}

fn main() {}
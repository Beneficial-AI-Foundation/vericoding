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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, t: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, d as int, t@.map(|_i: int, x: i8| x as int))
    ensures valid_result(n as int, d as int, t@.map(|_i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed compilation errors by changing 'int' variables to 'i32' and casting appropriately */
    let mut sum_t: i32 = 0;
    let mut i: usize = 0;
    while i < t.len()
        invariant
            i >= 0,
            i <= t.len(),
            sum_t as int == sum_seq(t@.map(|_, x| x as int).subrange(0, i as int)),
        decreases t.len() - i
    {
        sum_t += t[i] as i32;
        i += 1;
    }
    let n_int = n as i32;
    let d_int = d as i32;
    let min_time = sum_t + 10 * (n_int - 1);
    let result_i32 = if min_time > d_int {
        -1
    } else {
        (d_int - sum_t) / 5
    };
    result_i32 as i8
}
// </vc-code>


}

fn main() {}
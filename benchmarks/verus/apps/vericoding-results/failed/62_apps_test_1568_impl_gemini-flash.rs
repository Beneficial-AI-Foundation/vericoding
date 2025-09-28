// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int, c: int, t: int, arrivals: Seq<int>) -> bool {
    1 <= n <= 1000 &&
    1 <= a <= 1000 &&
    1 <= b <= 1000 &&
    1 <= c <= 1000 &&
    1 <= t <= 1000 &&
    arrivals.len() == n &&
    forall|i: int| 0 <= i < arrivals.len() ==> #[trigger] arrivals[i] >= 1 && #[trigger] arrivals[i] <= t
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn max_money(n: int, a: int, b: int, c: int, t: int, arrivals: Seq<int>) -> int {
    if b > c {
        n * a
    } else {
        n * a + (c - b) * (n * t - sum_seq(arrivals))
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8, t: i8, arrivals: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
    ensures result as int == max_money(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by replacing `fold` with explicit loop for `sum_arrivals`, and ensuring correct type conversions. */
    let mut total_money: i16 = 0;
    let n_i16 = n as i16;
    let a_i16 = a as i16;
    let b_i16 = b as i16;
    let c_i16 = c as i16;
    let t_i16 = t as i16;

    if b_i16 >= c_i16 {
        total_money = n_i16 * a_i16;
    } else {
        let mut sum_arrivals: i16 = 0;
        let mut i: usize = 0;
        while (i < arrivals.len())
            invariant
                0 <= i,
                i <= arrivals.len(),
                sum_arrivals == arrivals@.subrange(0, i as int).map_values(|x: i8| x as int).fold(0, |acc, val| acc + val) as i16,
            decreases arrivals.len() - i
        {
            sum_arrivals = sum_arrivals + arrivals[i] as i16;
            i = i + 1;
        }

        let total_late_time = n_i16 * t_i16 - sum_arrivals;
        total_money = n_i16 * a_i16 + (c_i16 - b_i16) * total_late_time;
    }
    total_money as i8
}
// </vc-code>


}

fn main() {}
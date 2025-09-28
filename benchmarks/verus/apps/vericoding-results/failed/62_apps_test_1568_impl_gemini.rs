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
fn compute_sum(arrivals: &Vec<i8>) -> (sum: i64)
    ensures
        sum as int == sum_seq(arrivals@.map_values(|x: i8| x as int)),
{
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < arrivals.len()
        invariant
            0 <= i <= arrivals.len(),
            sum as int == sum_seq(arrivals@.map_values(|x: i8| x as int).subrange(0, i as int)),
        decreases arrivals.len() - i
    {
        sum = sum + arrivals[i] as i64;
        i = i + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8, t: i8, arrivals: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
    ensures result as int == max_money(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let n_i64 = n as i64;
    let a_i64 = a as i64;
    let b_i64 = b as i64;
    let c_i64 = c as i64;
    let t_i64 = t as i64;

    let money = if b > c {
        n_i64 * a_i64
    } else {
        let sum_arrivals_i64 = compute_sum(&arrivals);
        n_i64 * a_i64 + (c_i64 - b_i64) * (n_i64 * t_i64 - sum_arrivals_i64)
    };
    
    money as i8
}
// </vc-code>


}

fn main() {}
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
proof fn sum_seq_bounds(s: Seq<int>, t: int)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 1 && s[i] <= t,
        t >= 1,
    ensures
        sum_seq(s) >= s.len(),
        sum_seq(s) <= t * s.len(),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        sum_seq_bounds(s.subrange(1, s.len() as int), t);
        assert(sum_seq(s) == s[0] + sum_seq(s.subrange(1, s.len() as int)));
        assert(s[0] >= 1);
        assert(s[0] <= t);
    }
}

proof fn arrivals_sum_bounds_from_valid(n: int, a: int, b: int, c: int, t: int, arrivals: Seq<int>)
    requires
        valid_input(n, a, b, c, t, arrivals),
    ensures
        sum_seq(arrivals) >= n,
        sum_seq(arrivals) <= n * t,
{
    assert(arrivals.len() == n);
    sum_seq_bounds(arrivals, t);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8, t: i8, arrivals: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
    ensures result as int == max_money(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let ni: int = n as int;
    let ai: int = a as int;
    let bi: int = b as int;
    let ci: int = c as int;
    let ti: int = t as int;
    let seq_arr: Seq<int> = arrivals@.map_values(|x: i8| x as int);

    proof {
        arrivals_sum_bounds_from_valid(ni, ai, bi, ci, ti, seq_arr);
    }

    let sum: int = sum_seq(seq_arr);
    let ans: int;
    if bi > ci {
        ans = ni * ai;
        proof {
            assert(max_money(ni, ai, bi, ci, ti, seq_arr) == ni * ai);
        }
    } else {
        ans = ni * ai + (ci - bi) * (ni * ti - sum);
        proof {
            assert(max_money(ni, ai, bi, ci, ti, seq_arr) == ni * ai + (ci - bi) * (ni * ti - sum_seq(seq_arr)));
        }
    }
    ans as i8
}
// </vc-code>


}

fn main() {}
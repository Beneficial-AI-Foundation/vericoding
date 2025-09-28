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
/* helper modified by LLM (iteration 5): fixed nat literal to use 0 instead of 0nat */
fn lemma_sum_seq_computation(arrivals: Seq<int>, n: int)
    requires arrivals.len() == n
    ensures sum_seq(arrivals) == arrivals.fold_left(0, |acc: int, x: int| acc + x)
    decreases arrivals.len()
{
    if arrivals.len() == 0 {
    } else {
        proof {
            lemma_sum_seq_computation(arrivals.subrange(1, arrivals.len() as int), n - 1);
        }
    }
}

fn lemma_sum_conversion(arrivals: Vec<i8>)
    ensures sum_seq(arrivals@.map_values(|x: i8| x as int)) == arrivals@.fold_left(0, |acc: int, x: i8| acc + x as int)
{
    proof {
        let mapped = arrivals@.map_values(|x: i8| x as int);
        lemma_sum_seq_computation(mapped, arrivals.len() as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8, t: i8, arrivals: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
    ensures result as int == max_money(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed nat literal and type annotations */
    let total_arrivals = arrivals.iter().fold(0i8, |acc, &x| acc + x);
    
    proof {
        lemma_sum_conversion(arrivals);
    }
    
    if b > c {
        n * a
    } else {
        let waiting_time = n * t - total_arrivals;
        let bonus = (c - b) * waiting_time;
        n * a + bonus
    }
}
// </vc-code>


}

fn main() {}
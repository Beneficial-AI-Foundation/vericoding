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

/* helper modified by LLM (iteration 5): fix subseq_sum type conversion and add proper spec helpers */
proof fn subseq_sum(s: Seq<int>, start: int, end: int) -> int
    requires 0 <= start <= end <= s.len()
    decreases end - start
{
    if start == end {
        0
    } else {
        s[start] + subseq_sum(s, start + 1, end)
    }
}

proof fn sum_seq_equals_subseq_sum(s: Seq<int>)
    ensures sum_seq(s) == subseq_sum(s, 0, s.len() as int)
    decreases s.len()
{
    if s.len() > 0 {
        sum_seq_equals_subseq_sum(s.subrange(1, s.len() as int));
    }
}

proof fn arrival_time_sum_properties(n: int, a: int, b: int, c: int, t: int, arrivals: Seq<int>)
    requires
        valid_input(n, a, b, c, t, arrivals),
    ensures
        sum_seq(arrivals) >= n,
        n * t - sum_seq(arrivals) >= 0
{
    assert forall|i: int| 0 <= i < arrivals.len() implies arrivals[i] >= 1 by {
        assert(valid_input(n, a, b, c, t, arrivals));
    };
    assert(sum_seq(arrivals) >= n);
    assert(n * t >= sum_seq(arrivals));
}

fn exec_subseq_sum(arrivals: &Vec<i8>, start: usize, end: usize) -> (sum_val: i16)
    requires
        start <= end <= arrivals.len()
    ensures
        sum_val as int == subseq_sum(arrivals@.map_values(|x: i8| x as int), start as int, end as int)
{
    let mut i = start;
    let mut sum_acc: i16 = 0;
    
    while i < end
        invariant
            i <= end,
            sum_acc as int == subseq_sum(arrivals@.map_values(|x: i8| x as int), start as int, i as int)
        decreases end - i
    {
        sum_acc = sum_acc + (arrivals[i] as i16);
        i = i + 1;
    }
    
    sum_acc
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8, t: i8, arrivals: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
    ensures result as int == max_money(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fix type conversion and subseq_sum call */
    let b_int = b as i16;
    let c_int = c as i16;
    
    if b_int > c_int {
        (n as i16 * a as i16) as i8
    } else {
        let n_int = n as i16;
        let a_int = a as i16;
        let t_int = t as i16;
        
        proof {
            let ghost_arrivals_seq = arrivals@.map_values(|x: i8| x as int);
            arrival_time_sum_properties(n as int, a as int, b as int, c as int, t as int, ghost_arrivals_seq);
            sum_seq_equals_subseq_sum(ghost_arrivals_seq);
        }
        
        let total_sum = exec_subseq_sum(&arrivals, 0, arrivals.len());
        let total_arrivals = n_int * t_int;
        let time_diff = total_arrivals - total_sum;
        let additional_money = (c_int - b_int) * time_diff;
        let base_money = n_int * a_int;
        
        (base_money + additional_money) as i8
    }
}
// </vc-code>


}

fn main() {}
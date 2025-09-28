// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: Seq<int>) -> bool {
    n >= 0 && m >= 0 && m == a.len()
}

spec fn can_complete_all_assignments(n: int, a: Seq<int>) -> bool {
    sum_seq(a) <= n
}

spec fn total_assignment_days(a: Seq<int>) -> int {
    sum_seq(a)
}

spec fn sum_seq(s: Seq<int>) -> int 
    decreases s.len()
{
    if s.len() == 0 { 
        0 
    } else { 
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sum_push(s: Seq<int>, x: int)
    ensures
        sum_seq(s.push(x)) == sum_seq(s) + x,
    decreases s.len()
{
    if s.len() > 0 {
        lemma_sum_push(s.subrange(1, s.len() as int), x);
    }
}

/* helper modified by LLM (iteration 4): addressed compilation error in map closure */
fn compute_sum(a: &Vec<i8>) -> (sum: i32)
    requires
        a.len() <= 127,
    ensures
        sum as int == total_assignment_days(a@.map(|i, x: i8| x as int)),
{
    let ghost a_int_seq = a@.map(|idx, val: i8| val as int);
    let mut i: usize = 0;
    let mut current_sum: i32 = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a@.map(|idx, val: i8| val as int) == a_int_seq,
            current_sum as int == sum_seq(a_int_seq.subrange(0, i as int)),
        decreases a.len() - i
    {
        proof {
            if i < a.len() {
                let sub_before = a_int_seq.subrange(0, i as int);
                assert(a_int_seq.subrange(0, (i + 1) as int) == sub_before.push(a_int_seq[i as int]));
                lemma_sum_push(sub_before, a_int_seq[i as int]);
            }
        }
        current_sum = current_sum + a[i] as i32;
        i = i + 1;
    }
    current_sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, a@.map(|i, x: i8| x as int))
    ensures 
        m as int == 0 ==> result as int == n as int,
        m as int > 0 && can_complete_all_assignments(n as int, a@.map(|i, x: i8| x as int)) ==> result as int == n as int - total_assignment_days(a@.map(|i, x: i8| x as int)),
        m as int > 0 && !can_complete_all_assignments(n as int, a@.map(|i, x: i8| x as int)) ==> result as int == -1,
        result as int >= -1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): addressed compilation error in map closure */
    if m == 0 {
        return n;
    }

    let total_days = compute_sum(&a);

    let ghost a_int_seq = a@.map(|i, x: i8| x as int);
    proof {
        assert(total_days as int == total_assignment_days(a_int_seq));
    }

    if total_days > n as i32 {
        proof {
            assert(!can_complete_all_assignments(n as int, a_int_seq));
        }
        return -1;
    } else {
        proof {
            assert(can_complete_all_assignments(n as int, a_int_seq));
        }
        let result = n as i32 - total_days;
        return result as i8;
    }
}
// </vc-code>


}

fn main() {}
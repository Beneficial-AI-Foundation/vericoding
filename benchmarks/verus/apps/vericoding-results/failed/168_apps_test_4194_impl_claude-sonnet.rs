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
/* helper modified by LLM (iteration 2): fixed lemma syntax by adding fn keyword */
fn lemma_sum_seq_nonneg(s: Seq<int>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    ensures
        sum_seq(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_sum_seq_nonneg(s.subrange(1, s.len() as int));
    }
}

fn lemma_sum_seq_append(s1: Seq<int>, s2: Seq<int>)
    ensures
        sum_seq(s1 + s2) == sum_seq(s1) + sum_seq(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 == s2);
    } else {
        lemma_sum_seq_append(s1.subrange(1, s1.len() as int), s2);
    }
}

fn compute_sum(a: Vec<i8>) -> (sum: i8)
    requires
        a@.len() >= 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i] >= 0
    ensures
        sum as int == sum_seq(a@.map(|i, x: i8| x as int))
{
    let mut sum = 0i8;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum as int == sum_seq(a@.subrange(0, i as int).map(|j, x: i8| x as int))
        decreases a.len() - i
    {
        sum = sum + a[i];
        
        proof {
            let prev_seq = a@.subrange(0, i as int).map(|j, x: i8| x as int);
            let new_seq = a@.subrange(0, (i + 1) as int).map(|j, x: i8| x as int);
            assert(new_seq == prev_seq.push(a@[i as int] as int));
        }
        
        i += 1;
    }
    
    proof {
        assert(a@.subrange(0, a@.len()) == a@);
    }
    
    sum
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
/* code modified by LLM (iteration 2): no changes needed as compilation error was in helpers */
{
    if m == 0 {
        return n;
    }
    
    let total_days = compute_sum(a);
    
    if total_days <= n {
        n - total_days
    } else {
        -1
    }
}
// </vc-code>


}

fn main() {}
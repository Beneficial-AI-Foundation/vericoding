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


spec fn map_sum_eq(s: Seq<int>) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + map_sum_eq(s.subrange(1, s.len() as int))
    }
}

proof fn sum_seq_equals_map_sum(s: Seq<int>)
    ensures
        sum_seq(s) == map_sum_eq(s),
    decreases s.len()
{
    if s.len() > 0 {
        sum_seq_equals_map_sum(s.subrange(1, s.len() as int));
    }
}

fn vec_fold_sum(vec: Vec<i8>) -> (total_days: i8)
    requires
        vec@.len() >= 0,
    ensures
        total_days as int == map_sum_eq(vec@.map(|i, x: i8| x as int)),
{
    /* helper modified by LLM (iteration 5): removed ghost type usage in executable code */
    let mut sum: i8 = 0;
    let mut index: usize = 0;
    
    while index < vec.len()
        invariant
            0 <= index <= vec.len(),
            sum as int == map_sum_eq(vec@.subrange(0, index as int).map(|i, x: i8| x as int)),
            sum >= 0,
        decreases vec.len() - index
    {
        let current = vec[index];
        sum = sum + current;
        proof {
            assert(current as int >= 0);
        }
        index = index + 1;
    }
    
    total_days
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
/* code modified by LLM (iteration 5): removed ghost type usage in executable code */
{
    let total_days = vec_fold_sum(a);
    
    proof {
        sum_seq_equals_map_sum(a@.map(|i, x: i8| x as int));
    }
    
    if m == 0 {
        n
    } else if total_days <= n {
        n - total_days
    } else {
        -1
    }
}
// </vc-code>


}

fn main() {}
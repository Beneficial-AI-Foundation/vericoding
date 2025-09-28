// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: int, v: Seq<int>) -> bool {
    n > 0 && v.len() == n && s >= 0 && forall|i: int| 0 <= i < v.len() ==> v[i] >= 0
}

spec fn sum(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        v[0] + sum(v.subrange(1, v.len() as int))
    }
}

spec fn min_seq(v: Seq<int>) -> int
    recommends v.len() > 0
    decreases v.len()
{
    if v.len() == 1 {
        v[0]
    } else if v.len() > 1 && v[0] <= min_seq(v.subrange(1, v.len() as int)) {
        v[0]
    } else if v.len() > 1 {
        min_seq(v.subrange(1, v.len() as int))
    } else {
        0
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed loop invariants and function postconditions to match recursion */
exec fn compute_sum(v: &Vec<i8>) -> (sum_val: i64)
    requires v@.len() > 0
    ensures sum_val == sum(v@.map(|i, x| x as int))
{
    let mut sum_val = 0;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum_val == sum(v@.subrange(0, i as int).map(|j, x| x as int))
        decreases v.len() - i
    {
        proof {
            assert(v@.subrange(0, (i+1) as int).map(|j, x| x as int) == v@.subrange(0, i as int).map(|j, x| x as int).push((v[i] as int)));
        }
        sum_val = sum_val + (v[i] as i64);
        i = i + 1;
    }
    sum_val
}

exec fn compute_min(v: &Vec<i8>) -> (min_val: i64)
    requires v@.len() > 0
    ensures min_val == min_seq(v@.map(|i, x| x as int))
{
    let mut min_val = v[0] as i64;
    let mut i = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            min_val == min_seq(v@.subrange(0, i as int).map(|j, x| x as int))
        decreases v.len() - i
    {
        proof {
            let current_seq = v@.subrange(0, i as int).map(|j, x| x as int);
            let next_seq = v@.subrange(0, (i+1) as int).map(|j, x| x as int);
            assert(next_seq == current_seq.push(v[i] as int));
        }
        if (v[i] as i64) < min_val {
            min_val = v[i] as i64;
        }
        i = i + 1;
    }
    min_val
}

proof fn lemma_sum_nonneg(v: Seq<int>)
    requires forall|i: int| 0 <= i < v.len() ==> v[i] >= 0
    ensures sum(v) >= 0
    decreases v.len()
{
    if v.len() == 0 {
    } else {
        lemma_sum_nonneg(v.subrange(1, v.len() as int));
    }
}

proof fn lemma_min_seq_bounds(v: Seq<int>)
    requires v.len() > 0
    ensures forall|i: int| 0 <= i < v.len() ==> min_seq(v) <= v[i]
    decreases v.len()
{
    if v.len() == 1 {
        assert(min_seq(v) == v[0]);
    } else if v.len() > 1 {
        lemma_min_seq_bounds(v.subrange(1, v.len() as int));
        if v[0] <= min_seq(v.subrange(1, v.len() as int)) {
            assert(min_seq(v) == v[0]);
        } else {
            assert(min_seq(v) == min_seq(v.subrange(1, v.len() as int)));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: i8, v: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, s as int, v@.map(|i, x| x as int))
    ensures 
        sum(v@.map(|i, x| x as int)) < s as int ==> result == -1,
        sum(v@.map(|i, x| x as int)) >= s as int ==> result == min((sum(v@.map(|i, x| x as int)) - s as int) / n as int, min_seq(v@.map(|i, x| x as int))) as i8,
        result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add explicit bounds checking and range assertions */
    let total_sum = compute_sum(&v);
    
    proof {
        let mapped_v = v@.map(|i, x| x as int);
        lemma_sum_nonneg(mapped_v);
        lemma_min_seq_bounds(mapped_v);
    }
    
    if total_sum < (s as i64) {
        -1
    } else {
        let diff = total_sum - (s as i64);
        let avg_reduce = diff / (n as i64);
        let min_val = compute_min(&v);
        
        let result_val = if avg_reduce <= min_val { avg_reduce } else { min_val };
        
        proof {
            assert(result_val >= 0);
            assert(result_val <= 127); // i8 max value
        }
        
        #[verifier::truncate]
        (result_val as i8)
    }
}
// </vc-code>


}

fn main() {}
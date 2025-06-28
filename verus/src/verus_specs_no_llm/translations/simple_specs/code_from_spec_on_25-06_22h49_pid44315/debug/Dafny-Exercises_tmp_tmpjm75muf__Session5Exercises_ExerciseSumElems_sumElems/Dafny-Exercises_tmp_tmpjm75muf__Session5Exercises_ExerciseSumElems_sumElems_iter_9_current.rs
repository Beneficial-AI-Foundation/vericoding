use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SumL(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        v[0] + SumL(v.subrange(1, v.len() as int))
    }
}

spec fn SumR(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        SumR(v.subrange(0, (v.len() - 1) as int)) + v[v.len() - 1]
    }
}

spec fn SumV(v: Vec<int>, start: int, end: int) -> int
    recommends 0 <= start <= end <= v.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        v[start] + SumV(v, start + 1, end)
    }
}

proof fn sum_equivalence(v: Seq<int>)
    ensures SumL(v) == SumR(v)
    decreases v.len()
{
    if v.len() <= 1 {
        // Base cases: empty sequence or single element
    } else {
        // Inductive case
        let left_tail = v.subrange(1, v.len() as int);
        let right_init = v.subrange(0, (v.len() - 1) as int);
        
        // Apply induction hypothesis to subsequences
        sum_equivalence(left_tail);
        sum_equivalence(right_init);
        
        // The key insight: both compute the same sum
        // SumL(v) = v[0] + SumL(tail) = v[0] + SumR(tail) (by IH on tail)
        // SumR(v) = SumR(init) + v[last] = SumL(init) + v[last] (by IH on init)
        // We need to show v[0] + SumR(tail) = SumL(init) + v[last]
        sum_middle_equivalence(v);
    }
}

proof fn sum_middle_equivalence(v: Seq<int>)
    requires v.len() >= 2
    ensures v[0] + SumR(v.subrange(1, v.len() as int)) == 
            SumL(v.subrange(0, (v.len() - 1) as int)) + v[v.len() - 1]
    decreases v.len()
{
    if v.len() == 2 {
        // Base case: for sequence [a, b]
        // Left side: a + SumR([b]) = a + b
        // Right side: SumL([a]) + b = a + b
        let tail = v.subrange(1, 2);
        let init = v.subrange(0, 1);
        assert(tail.len() == 1);
        assert(init.len() == 1);
        assert(SumR(tail) == tail[0]);
        assert(SumL(init) == init[0]);
        assert(tail[0] == v[1]);
        assert(init[0] == v[0]);
    } else {
        // For longer sequences, both sides represent the sum of all elements
        // Use the fact that both expressions equal the total sum
        let tail = v.subrange(1, v.len() as int);
        let init = v.subrange(0, (v.len() - 1) as int);
        
        sum_equivalence(tail);
        sum_equivalence(init);
        
        // Both SumL and SumR compute the same sum for any sequence
        assert(SumR(tail) == SumL(tail));
        assert(SumL(init) == SumR(init));
        
        // The middle part is computed the same way in both expressions
        sum_total_equivalence(v);
    }
}

proof fn sum_total_equivalence(v: Seq<int>)
    requires v.len() >= 2
    ensures v[0] + SumL(v.subrange(1, v.len() as int)) == 
            SumL(v.subrange(0, (v.len() - 1) as int)) + v[v.len() - 1]
{
    // Both expressions represent the sum of all elements in v
    // This follows from the distributive property of addition
    let n = v.len();
    let tail = v.subrange(1, n as int);
    let init = v.subrange(0, (n - 1) as int);
    
    sum_equivalence(tail);
    sum_equivalence(init);
}

proof fn sum_v_equivalence(v: Vec<int>)
    ensures SumV(v, 0, v.len() as int) == SumL(v.as_seq())
    decreases v.len()
{
    sum_v_seq_helper(v, 0, v.len() as int);
}

proof fn sum_v_seq_helper(v: Vec<int>, start: int, end: int)
    requires 0 <= start <= end <= v.len()
    ensures SumV(v, start, end) == SumL(v.as_seq().subrange(start, end))
    decreases end - start
{
    if start >= end {
        assert(v.as_seq().subrange(start, end).len() == 0);
    } else {
        sum_v_seq_helper(v, start + 1, end);
        let subseq = v.as_seq().subrange(start, end);
        assert(subseq[0] == v[start]);
        assert(subseq.subrange(1, (end - start) as int) == 
               v.as_seq().subrange(start + 1, end));
    }
}

proof fn sum_v_step(v: Vec<int>, i: int)
    requires 0 <= i < v.len()
    ensures SumV(v, 0, i) + v[i] == SumV(v, 0, i + 1)
{
    sum_v_step_helper(v, 0, i);
}

proof fn sum_v_step_helper(v: Vec<int>, start: int, end: int)
    requires 0 <= start <= end < v.len()
    ensures SumV(v, start, end) + v[end] == SumV(v, start, end + 1)
    decreases end - start
{
    if start == end {
        // Base case: SumV(v, end, end) + v[end] == 0 + v[end] == v[end] == SumV(v, end, end + 1)
    } else {
        sum_v_step_helper(v, start + 1, end);
    }
}

fn sumElems(v: Vec<int>) -> (sum: int)
    ensures
        sum == SumL(v.as_seq()),
        sum == SumR(v.as_seq()),
        sum == SumV(v, 0, v.len() as int)
{
    proof {
        sum_equivalence(v.as_seq());
        sum_v_equivalence(v);
    }
    
    let mut i: usize = 0;
    let mut result = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result == SumV(v, 0, i as int)
    {
        proof {
            sum_v_step(v, i as int);
        }
        result = result + v[i];
        i = i + 1;
    }
    
    result
}

}
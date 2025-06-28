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
        // For sequences with length > 1
        let v_without_first = v.subrange(1, v.len() as int);
        let v_without_last = v.subrange(0, (v.len() - 1) as int);
        
        // Apply inductive hypothesis
        sum_equivalence(v_without_first);
        sum_equivalence(v_without_last);
        
        // The proof works by structural induction
        assert(SumL(v) == v[0] + SumL(v_without_first));
        assert(SumR(v) == SumR(v_without_last) + v[v.len() - 1]);
        
        // By inductive hypothesis, we need to show that:
        // v[0] + SumL(v_without_first) == SumR(v_without_last) + v[v.len() - 1]
        // This follows from the fact that v_without_first and v_without_last
        // represent the same middle elements when v.len() > 1
    }
}

proof fn sum_v_equivalence(v: Vec<int>)
    ensures SumV(v, 0, v.len() as int) == SumL(v.as_seq())
    decreases v.len()
{
    sum_v_equivalence_helper(v, 0);
}

proof fn sum_v_equivalence_helper(v: Vec<int>, start: int)
    requires 0 <= start <= v.len()
    ensures SumV(v, start, v.len() as int) == SumL(v.as_seq().subrange(start, v.len() as int))
    decreases v.len() - start
{
    if start >= v.len() {
        // Base case: empty range
    } else {
        // Recursive case
        sum_v_equivalence_helper(v, start + 1);
        
        let subseq = v.as_seq().subrange(start, v.len() as int);
        assert(subseq[0] == v[start]);
        assert(subseq.subrange(1, subseq.len() as int) == v.as_seq().subrange(start + 1, v.len() as int));
    }
}

proof fn sum_v_step(v: Vec<int>, i: int)
    requires 0 <= i < v.len()
    ensures SumV(v, 0, i) + v[i] == SumV(v, 0, i + 1)
    decreases i
{
    if i == 0 {
        // Base case
    } else {
        // Recursive case: use the definition and induction
        sum_v_step_helper(v, 1, i);
    }
}

proof fn sum_v_step_helper(v: Vec<int>, start: int, end: int)
    requires 0 <= start <= end < v.len()
    ensures SumV(v, start, end) + v[end] == SumV(v, start, end + 1)
    decreases end - start
{
    if start == end {
        // Base case: empty range plus one element
    } else {
        // Recursive case
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
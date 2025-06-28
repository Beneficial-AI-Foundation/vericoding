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
        let head = v[0];
        let last = v[v.len() - 1];
        let v_without_first = v.subrange(1, v.len() as int);
        let v_without_last = v.subrange(0, (v.len() - 1) as int);
        
        // Apply inductive hypothesis
        sum_equivalence(v_without_first);
        sum_equivalence(v_without_last);
        
        // For the middle part (without first and last elements)
        if v.len() > 2 {
            let v_middle = v.subrange(1, (v.len() - 1) as int);
            sum_equivalence(v_middle);
            
            // Show that both SumL and SumR compute the same thing
            assert(SumL(v) == head + SumL(v_without_first));
            assert(SumR(v) == SumR(v_without_last) + last);
            
            // The key insight: v_without_first and v_without_last overlap in the middle
            assert(SumL(v_without_first) == v[1] + SumL(v.subrange(2, v.len() as int)));
            assert(SumR(v_without_last) == SumR(v.subrange(0, (v.len() - 2) as int)) + v[v.len() - 2]);
            
            // By the structure of sequences and inductive hypothesis
            assert(SumL(v.subrange(2, v.len() as int)) == SumR(v.subrange(2, v.len() as int)));
        }
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
        assert(v.as_seq().subrange(start, v.len() as int).len() == 0);
        assert(SumV(v, start, v.len() as int) == 0);
        assert(SumL(v.as_seq().subrange(start, v.len() as int)) == 0);
    } else {
        // Recursive case
        sum_v_equivalence_helper(v, start + 1);
        
        // Both expand the same way
        assert(SumV(v, start, v.len() as int) == v[start] + SumV(v, start + 1, v.len() as int));
        
        let subseq = v.as_seq().subrange(start, v.len() as int);
        assert(subseq.len() > 0);
        assert(SumL(subseq) == subseq[0] + SumL(subseq.subrange(1, subseq.len() as int)));
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
        assert(SumV(v, 0, 0) == 0);
        assert(SumV(v, 0, 1) == v[0] + SumV(v, 1, 1));
        assert(SumV(v, 1, 1) == 0);
    } else {
        // Use the recursive definition
        assert(SumV(v, 0, i) == v[0] + SumV(v, 1, i));
        assert(SumV(v, 0, i + 1) == v[0] + SumV(v, 1, i + 1));
        
        // Show that SumV(v, 1, i) + v[i] == SumV(v, 1, i + 1)
        sum_v_step_helper(v, 1, i);
    }
}

proof fn sum_v_step_helper(v: Vec<int>, start: int, end: int)
    requires 0 <= start <= end < v.len()
    ensures SumV(v, start, end) + v[end] == SumV(v, start, end + 1)
    decreases end - start
{
    if start == end {
        assert(SumV(v, start, end) == 0);
        assert(SumV(v, start, end + 1) == v[start] + SumV(v, start + 1, end + 1));
        assert(SumV(v, start + 1, end + 1) == 0);
        assert(v[start] == v[end]);
    } else {
        assert(SumV(v, start, end) == v[start] + SumV(v, start + 1, end));
        assert(SumV(v, start, end + 1) == v[start] + SumV(v, start + 1, end + 1));
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
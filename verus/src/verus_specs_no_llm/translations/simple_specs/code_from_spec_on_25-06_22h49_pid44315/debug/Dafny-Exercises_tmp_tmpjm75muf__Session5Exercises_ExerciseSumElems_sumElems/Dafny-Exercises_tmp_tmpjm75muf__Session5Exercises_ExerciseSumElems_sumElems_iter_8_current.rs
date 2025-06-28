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
        
        // Use lemma to connect the two approaches
        sum_split_equivalence(v);
    }
}

proof fn sum_split_equivalence(v: Seq<int>)
    requires v.len() >= 2
    ensures v[0] + SumL(v.subrange(1, v.len() as int)) == 
            SumR(v.subrange(0, (v.len() - 1) as int)) + v[v.len() - 1]
    decreases v.len()
{
    if v.len() == 2 {
        // Base case: for sequence [a, b]
        // Left side: a + SumL([b]) = a + b
        // Right side: SumR([a]) + b = a + b
        assert(v.subrange(1, 2).len() == 1);
        assert(v.subrange(0, 1).len() == 1);
    } else {
        // For longer sequences, use the fact that both expressions
        // compute the sum of all elements in v
        sum_equivalence(v.subrange(1, v.len() as int));
        sum_equivalence(v.subrange(0, (v.len() - 1) as int));
        
        // The middle portion is the same in both cases
        let middle = v.subrange(1, (v.len() - 1) as int);
        sum_equivalence(middle);
        
        // Both sides equal v[0] + sum(middle) + v[last]
        assert(SumL(v.subrange(1, v.len() as int)) == 
               v[1] + SumL(v.subrange(2, v.len() as int)));
        assert(SumR(v.subrange(0, (v.len() - 1) as int)) == 
               SumR(v.subrange(0, (v.len() - 2) as int)) + v[v.len() - 2]);
    }
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
        assert(v.as_seq().subrange(start, end)[0] == v[start]);
        assert(v.as_seq().subrange(start, end).subrange(1, (end - start) as int) == 
               v.as_seq().subrange(start + 1, end));
    }
}

proof fn sum_v_step(v: Vec<int>, i: int)
    requires 0 <= i < v.len()
    ensures SumV(v, 0, i) + v[i] == SumV(v, 0, i + 1)
{
    if i == 0 {
        // Base case
    } else {
        sum_v_step_helper(v, 1, i);
    }
}

proof fn sum_v_step_helper(v: Vec<int>, start: int, end: int)
    requires 0 <= start <= end < v.len()
    ensures SumV(v, start, end) + v[end] == SumV(v, start, end + 1)
    decreases end - start
{
    if start == end {
        // Base case
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
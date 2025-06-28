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
        if v.len() == 0 {
            assert(SumL(v) == 0);
            assert(SumR(v) == 0);
        } else {
            assert(v.len() == 1);
            assert(SumL(v) == v[0]);
            assert(SumR(v) == v[0]);
        }
    } else {
        // For sequences with length > 1
        let mid_seq = v.subrange(1, (v.len() - 1) as int);
        
        // Apply inductive hypothesis to the middle part
        sum_equivalence(mid_seq);
        
        // Establish the equivalence by showing both sides equal v[0] + SumL(mid_seq) + v[v.len()-1]
        assert(SumL(v) == v[0] + SumL(v.subrange(1, v.len() as int)));
        assert(SumR(v) == SumR(v.subrange(0, (v.len() - 1) as int)) + v[v.len() - 1]);
        
        // Show that the middle parts are equivalent
        sum_left_right_shift(v.subrange(1, v.len() as int), v.subrange(0, (v.len() - 1) as int));
    }
}

proof fn sum_left_right_shift(left_seq: Seq<int>, right_seq: Seq<int>)
    requires left_seq.len() == right_seq.len()
    requires forall|i: int| 0 <= i < left_seq.len() ==> left_seq[i] == right_seq[i]
    ensures SumL(left_seq) == SumR(right_seq)
    decreases left_seq.len()
{
    if left_seq.len() == 0 {
        assert(SumL(left_seq) == 0);
        assert(SumR(right_seq) == 0);
    } else {
        sum_equivalence(left_seq);
        sum_equivalence(right_seq);
        assert(SumL(left_seq) == SumR(left_seq));
        assert(SumL(right_seq) == SumR(right_seq));
        
        // Since sequences are equal, their sums are equal
        sum_equal_sequences(left_seq, right_seq);
    }
}

proof fn sum_equal_sequences(s1: Seq<int>, s2: Seq<int>)
    requires s1 =~= s2
    ensures SumL(s1) == SumL(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(SumL(s1) == 0);
        assert(SumL(s2) == 0);
    } else {
        assert(s1[0] == s2[0]);
        let s1_rest = s1.subrange(1, s1.len() as int);
        let s2_rest = s2.subrange(1, s2.len() as int);
        assert(s1_rest =~= s2_rest);
        sum_equal_sequences(s1_rest, s2_rest);
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
        assert(SumV(v, start, v.len() as int) == 0);
        assert(v.as_seq().subrange(start, v.len() as int).len() == 0);
        assert(SumL(v.as_seq().subrange(start, v.len() as int)) == 0);
    } else {
        // Recursive case
        sum_v_equivalence_helper(v, start + 1);
        
        let subseq = v.as_seq().subrange(start, v.len() as int);
        assert(subseq.len() > 0);
        assert(subseq[0] == v[start]);
        assert(subseq.subrange(1, subseq.len() as int) == v.as_seq().subrange(start + 1, v.len() as int));
        
        assert(SumV(v, start, v.len() as int) == v[start] + SumV(v, start + 1, v.len() as int));
        assert(SumL(subseq) == subseq[0] + SumL(subseq.subrange(1, subseq.len() as int)));
    }
}

proof fn sum_v_step(v: Vec<int>, i: int)
    requires 0 <= i < v.len()
    ensures SumV(v, 0, i) + v[i] == SumV(v, 0, i + 1)
    decreases i
{
    if i == 0 {
        // Base case
        assert(SumV(v, 0, 0) == 0);
        assert(SumV(v, 0, 1) == v[0]);
        assert(SumV(v, 0, 0) + v[0] == SumV(v, 0, 1));
    } else {
        // Recursive case
        sum_v_step(v, i - 1);
        assert(SumV(v, 0, i) == v[0] + SumV(v, 1, i));
        assert(SumV(v, 0, i + 1) == v[0] + SumV(v, 1, i + 1));
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
        assert(SumV(v, start, end) == 0);
        assert(SumV(v, start, end + 1) == v[end]);
    } else {
        // Recursive case
        sum_v_step_helper(v, start + 1, end);
        assert(SumV(v, start, end) == v[start] + SumV(v, start + 1, end));
        assert(SumV(v, start, end + 1) == v[start] + SumV(v, start + 1, end + 1));
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
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
        // Inductive case
        let tail = v.subrange(1, v.len() as int);
        let init = v.subrange(0, (v.len() - 1) as int);
        
        // Apply induction hypothesis
        sum_equivalence(tail);
        sum_equivalence(init);
        
        // Show the relationship between the parts
        assert(SumL(v) == v[0] + SumL(tail));
        assert(SumR(v) == SumR(init) + v[v.len() - 1]);
        
        // Use the fact that both represent the same sum
        sum_parts_equal(v, init, tail);
    }
}

proof fn sum_parts_equal(v: Seq<int>, init: Seq<int>, tail: Seq<int>)
    requires 
        v.len() >= 2,
        init == v.subrange(0, (v.len() - 1) as int),
        tail == v.subrange(1, v.len() as int),
        SumL(tail) == SumR(tail),
        SumL(init) == SumR(init)
    ensures v[0] + SumL(tail) == SumR(init) + v[v.len() - 1]
{
    if v.len() == 2 {
        // Base case: v = [a, b]
        // tail = [b], init = [a]
        // Left: a + SumL([b]) = a + b
        // Right: SumR([a]) + b = a + b
        assert(tail.len() == 1 && init.len() == 1);
        assert(SumL(tail) == tail[0]);
        assert(SumR(init) == init[0]);
        assert(tail[0] == v[1]);
        assert(init[0] == v[0]);
        assert(v[1] == v[v.len() - 1]);
    } else {
        // For longer sequences, use induction on the middle part
        let middle = v.subrange(1, (v.len() - 1) as int);
        sum_equivalence(middle);
        
        // Break down the sums
        assert(SumL(tail) == tail[0] + SumL(tail.subrange(1, tail.len() as int)));
        assert(SumR(init) == SumR(init.subrange(0, (init.len() - 1) as int)) + init[init.len() - 1]);
        
        // The middle parts are the same
        assert(tail.subrange(1, tail.len() as int) == middle);
        assert(init.subrange(0, (init.len() - 1) as int) == middle);
        assert(tail[0] == v[1]);
        assert(init[init.len() - 1] == v[v.len() - 2]);
        
        // Recursively apply to the reduced problem
        let v_middle = v.subrange(1, (v.len() - 1) as int);
        if v_middle.len() >= 2 {
            let init_middle = v_middle.subrange(0, (v_middle.len() - 1) as int);
            let tail_middle = v_middle.subrange(1, v_middle.len() as int);
            sum_parts_equal(v_middle, init_middle, tail_middle);
        }
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
        let subseq = v.as_seq().subrange(start, end);
        assert(subseq.len() == 0);
        assert(SumL(subseq) == 0);
        assert(SumV(v, start, end) == 0);
    } else {
        sum_v_seq_helper(v, start + 1, end);
        let subseq = v.as_seq().subrange(start, end);
        assert(subseq.len() > 0);
        assert(subseq[0] == v[start]);
        let tail_subseq = subseq.subrange(1, subseq.len() as int);
        let expected_tail = v.as_seq().subrange(start + 1, end);
        assert(tail_subseq =~= expected_tail);
        assert(SumL(subseq) == subseq[0] + SumL(tail_subseq));
        assert(SumV(v, start, end) == v[start] + SumV(v, start + 1, end));
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
        assert(SumV(v, start, end) == 0);
        assert(SumV(v, start, end + 1) == v[end]);
    } else {
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
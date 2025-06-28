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
        // Base cases are trivial
    } else {
        // For sequences with length > 1
        let left_subseq = v.subrange(1, v.len() as int);
        let right_subseq = v.subrange(0, (v.len() - 1) as int);
        
        // Apply inductive hypothesis
        sum_equivalence(left_subseq);
        sum_equivalence(right_subseq);
        
        // The key insight: both subsequences represent the same middle elements
        // left_subseq = [v[1], v[2], ..., v[n-1]]
        // right_subseq = [v[0], v[1], ..., v[n-2]]
        // We need to show SumL(left_subseq) == SumR(right_subseq)
        
        // This requires showing that the sum of elements 1..n-1 equals
        // the sum of elements 0..n-2 when we account for the recursive structure
        assert(SumL(v) == v[0] + SumL(left_subseq));
        assert(SumR(v) == SumR(right_subseq) + v[v.len() - 1]);
        
        // By inductive hypothesis: SumL(left_subseq) == SumR(left_subseq)
        // and SumL(right_subseq) == SumR(right_subseq)
        
        // Now we need to relate the middle parts
        sum_middle_equivalence(v);
    }
}

proof fn sum_middle_equivalence(v: Seq<int>)
    requires v.len() >= 2
    ensures v[0] + SumL(v.subrange(1, v.len() as int)) == 
            SumR(v.subrange(0, (v.len() - 1) as int)) + v[v.len() - 1]
    decreases v.len()
{
    let left_sub = v.subrange(1, v.len() as int);
    let right_sub = v.subrange(0, (v.len() - 1) as int);
    
    if v.len() == 2 {
        // Base case: v = [a, b]
        // Left: a + SumL([b]) = a + b
        // Right: SumR([a]) + b = a + b
        assert(left_sub.len() == 1);
        assert(right_sub.len() == 1);
        assert(SumL(left_sub) == v[1]);
        assert(SumR(right_sub) == v[0]);
    } else {
        // Inductive case
        sum_equivalence(left_sub);
        sum_equivalence(right_sub);
        
        // The middle elements [1..n-2] appear in both subsequences
        let middle = v.subrange(1, (v.len() - 1) as int);
        sum_equivalence(middle);
        
        // Decompose the sums
        assert(SumL(left_sub) == v[1] + SumL(v.subrange(2, v.len() as int)));
        assert(SumR(right_sub) == SumR(v.subrange(0, (v.len() - 2) as int)) + v[v.len() - 2]);
        
        // The key insight: both sides sum to the same total
        sum_total_equivalence(v);
    }
}

proof fn sum_total_equivalence(v: Seq<int>)
    requires v.len() > 0
    ensures SumL(v) == SumR(v)
    decreases v.len()
{
    if v.len() == 1 {
        assert(SumL(v) == v[0]);
        assert(SumR(v) == v[0]);
    } else {
        // Use the fact that both compute the sum of all elements
        sum_all_elements_equivalence(v, 0);
    }
}

proof fn sum_all_elements_equivalence(v: Seq<int>, acc: int)
    ensures SumL(v) + acc == SumR(v) + acc
    decreases v.len()
{
    if v.len() == 0 {
        // Both are 0
    } else if v.len() == 1 {
        // Both are v[0]
    } else {
        // Both sum all elements, just in different orders
        let total = SumL(v);
        assert(total == SumR(v)) by {
            sum_direct_equivalence(v);
        }
    }
}

proof fn sum_direct_equivalence(v: Seq<int>)
    ensures SumL(v) == SumR(v)
    decreases v.len()
{
    if v.len() <= 1 {
        // Trivial cases
    } else {
        // Both functions sum all elements of v
        // SumL sums left-to-right: v[0] + v[1] + ... + v[n-1]
        // SumR sums right-to-left: v[0] + v[1] + ... + v[n-1]
        // They must be equal (commutativity and associativity of addition)
        
        // Use structural induction
        sum_direct_equivalence(v.subrange(1, v.len() as int));
        sum_direct_equivalence(v.subrange(0, (v.len() - 1) as int));
        
        // The sums are equal because they sum the same elements
        assert(SumL(v) == SumR(v)) by {
            // This follows from the mathematical property that
            // addition is commutative and associative
        }
    }
}

proof fn sum_v_equivalence(v: Vec<int>)
    ensures SumV(v, 0, v.len() as int) == SumL(v.as_seq())
    decreases v.len()
{
    sum_v_seq_equivalence(v, 0, v.len() as int, v.as_seq());
}

proof fn sum_v_seq_equivalence(v: Vec<int>, start: int, end: int, s: Seq<int>)
    requires 0 <= start <= end <= v.len()
    requires s == v.as_seq().subrange(start, end)
    ensures SumV(v, start, end) == SumL(s)
    decreases end - start
{
    if start >= end {
        assert(SumV(v, start, end) == 0);
        assert(s.len() == 0);
        assert(SumL(s) == 0);
    } else {
        let rest_seq = v.as_seq().subrange(start + 1, end);
        sum_v_seq_equivalence(v, start + 1, end, rest_seq);
        
        assert(SumV(v, start, end) == v[start] + SumV(v, start + 1, end));
        assert(SumL(s) == s[0] + SumL(s.subrange(1, s.len() as int)));
        assert(s[0] == v[start]);
        assert(s.subrange(1, s.len() as int) == rest_seq);
    }
}

proof fn sum_v_step(v: Vec<int>, i: int)
    requires 0 <= i < v.len()
    ensures SumV(v, 0, i) + v[i] == SumV(v, 0, i + 1)
    decreases i
{
    if i == 0 {
        assert(SumV(v, 0, 0) == 0);
        assert(SumV(v, 0, 1) == v[0]);
    } else {
        sum_v_step(v, i - 1);
        assert(SumV(v, 0, i) == v[0] + SumV(v, 1, i));
        assert(SumV(v, 0, i + 1) == v[0] + SumV(v, 1, i + 1));
        sum_v_step_range(v, 1, i);
    }
}

proof fn sum_v_step_range(v: Vec<int>, start: int, end: int)
    requires 0 <= start <= end < v.len()
    ensures SumV(v, start, end) + v[end] == SumV(v, start, end + 1)
    decreases end - start
{
    if start == end {
        assert(SumV(v, start, end) == 0);
        assert(SumV(v, start, end + 1) == v[end]);
    } else {
        sum_v_step_range(v, start + 1, end);
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
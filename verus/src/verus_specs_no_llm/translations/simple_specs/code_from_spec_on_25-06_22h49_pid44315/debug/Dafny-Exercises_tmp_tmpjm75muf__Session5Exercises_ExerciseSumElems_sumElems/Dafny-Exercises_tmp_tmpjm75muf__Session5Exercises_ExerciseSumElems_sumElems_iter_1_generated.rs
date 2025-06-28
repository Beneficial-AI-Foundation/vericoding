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
        SumR(v.subrange(0, v.len() - 1)) + v[v.len() - 1]
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
    if v.len() == 0 {
        // Base case: both are 0
    } else if v.len() == 1 {
        // Base case: both equal v[0]
    } else {
        // Inductive case
        let v_middle = v.subrange(1, v.len() - 1);
        sum_equivalence(v_middle);
        // SumL(v) = v[0] + SumL(v[1..])
        // SumR(v) = SumR(v[..len-1]) + v[len-1]
        // By induction, SumL and SumR are equal on the middle portion
    }
}

proof fn sum_v_equivalence(v: Vec<int>)
    ensures SumV(v, 0, v.len()) == SumL(v.as_seq())
    decreases v.len()
{
    if v.len() == 0 {
        // Both are 0
    } else {
        // SumV(v, 0, n) = v[0] + SumV(v, 1, n)
        // SumL(v.as_seq()) = v[0] + SumL(v.as_seq()[1..])
        sum_v_equivalence_helper(v, 1);
    }
}

proof fn sum_v_equivalence_helper(v: Vec<int>, start: int)
    requires 0 <= start <= v.len()
    ensures SumV(v, start, v.len()) == SumL(v.as_seq().subrange(start, v.len() as int))
    decreases v.len() - start
{
    if start >= v.len() {
        // Both are 0
    } else {
        sum_v_equivalence_helper(v, start + 1);
    }
}

fn sumElems(v: Vec<int>) -> (sum: int)
    ensures
        sum == SumL(v.spec_index(0..v.len())),
        sum == SumR(v.spec_index(..)),
        sum == SumV(v, 0, v.len())
{
    proof {
        sum_equivalence(v.as_seq());
        sum_v_equivalence(v);
    }
    
    let mut i = 0;
    let mut result = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result == SumV(v, 0, i)
    {
        result = result + v[i];
        i = i + 1;
    }
    
    result
}

}
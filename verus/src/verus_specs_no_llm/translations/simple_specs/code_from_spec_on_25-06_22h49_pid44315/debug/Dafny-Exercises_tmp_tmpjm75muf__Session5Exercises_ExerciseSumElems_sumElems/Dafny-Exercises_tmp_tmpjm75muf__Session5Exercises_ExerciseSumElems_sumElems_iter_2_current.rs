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
        assert(SumL(v) == v[0] + SumL(v.subrange(1, 1)));
        assert(SumL(v.subrange(1, 1)) == 0);
        assert(SumR(v) == SumR(v.subrange(0, 0)) + v[0]);
        assert(SumR(v.subrange(0, 0)) == 0);
    } else {
        // Inductive case
        let v_left = v.subrange(1, v.len() as int);
        let v_right = v.subrange(0, v.len() - 1);
        sum_equivalence(v_left);
        sum_equivalence(v_right);
        
        // Additional proof steps to connect the equivalence
        let v_middle = v.subrange(1, v.len() - 1);
        if v_middle.len() > 0 {
            sum_equivalence(v_middle);
        }
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
        assert(SumV(v, 1, v.len()) == SumL(v.as_seq().subrange(1, v.len() as int)));
    }
}

proof fn sum_v_equivalence_helper(v: Vec<int>, start: int)
    requires 0 <= start <= v.len()
    ensures SumV(v, start, v.len()) == SumL(v.as_seq().subrange(start, v.len() as int))
    decreases v.len() - start
{
    if start >= v.len() {
        // Both are 0
        assert(v.as_seq().subrange(start, v.len() as int).len() == 0);
    } else {
        sum_v_equivalence_helper(v, start + 1);
        assert(SumV(v, start + 1, v.len()) == SumL(v.as_seq().subrange(start + 1, v.len() as int)));
        // Connect the recursive calls
        assert(SumV(v, start, v.len()) == v[start] + SumV(v, start + 1, v.len()));
        assert(SumL(v.as_seq().subrange(start, v.len() as int)) == 
               v.as_seq().subrange(start, v.len() as int)[0] + 
               SumL(v.as_seq().subrange(start, v.len() as int).subrange(1, (v.len() - start) as int)));
        assert(v.as_seq().subrange(start, v.len() as int)[0] == v[start]);
        assert(v.as_seq().subrange(start, v.len() as int).subrange(1, (v.len() - start) as int) ==
               v.as_seq().subrange(start + 1, v.len() as int));
    }
}

fn sumElems(v: Vec<int>) -> (sum: int)
    ensures
        sum == SumL(v.as_seq()),
        sum == SumR(v.as_seq()),
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
        
        proof {
            // Help verify the loop invariant
            assert(result == SumV(v, 0, i));
        }
    }
    
    result
}

}
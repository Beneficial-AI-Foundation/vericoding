use builtin::*;
use builtin_macros::*;

verus! {

// Left-to-right sum (recursive)
spec fn SumL(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + SumL(s.subrange(1, s.len() as int))
    }
}

// Right-to-left sum (recursive)
spec fn SumR(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        SumR(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

// Lemma to prove that SumL and SumR are equivalent
proof fn lemma_sum_equivalence(s: Seq<int>)
    ensures SumL(s) == SumR(s)
    decreases s.len()
{
    if s.len() == 0 {
        // Base case: both return 0
    } else if s.len() == 1 {
        // Base case: both return s[0]
        assert(s.subrange(1, s.len() as int).len() == 0);
        assert(s.subrange(0, s.len() - 1).len() == 0);
    } else {
        // Inductive case
        let s_without_first = s.subrange(1, s.len() as int);
        let s_without_last = s.subrange(0, s.len() - 1);
        
        lemma_sum_equivalence(s_without_first);
        lemma_sum_equivalence(s_without_last);
        
        // Additional proof steps to show the equivalence
        assert(SumL(s) == s[0] + SumL(s_without_first));
        assert(SumR(s) == SumR(s_without_last) + s[s.len() - 1]);
        
        // Use the fact that both middle parts are equal
        lemma_sum_middle(s);
    }
}

// Helper lemma for the middle part equivalence
proof fn lemma_sum_middle(s: Seq<int>)
    requires s.len() >= 2
    ensures SumL(s.subrange(1, s.len() as int)) == SumR(s.subrange(0, s.len() - 1)) + s[0] - s[s.len() - 1]
{
    lemma_sum_equivalence(s.subrange(1, s.len() - 1));
}

fn sumElemsB(v: Vec<int>) -> (sum: int)
    ensures
        sum == SumL(v@),
        sum == SumR(v@)
{
    proof {
        lemma_sum_equivalence(v@);
    }
    
    let mut total = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            total == SumL(v@.subrange(0, i as int))
    {
        proof {
            assert(v@.subrange(0, i as int + 1) == v@.subrange(0, i as int).push(v[i as int]));
            lemma_sum_push(v@.subrange(0, i as int), v[i as int]);
        }
        total = total + v[i];
        i = i + 1;
    }
    
    proof {
        assert(i == v.len());
        assert(v@.subrange(0, i as int) == v@);
    }
    
    total
}

// Helper lemma for sequence push operation
proof fn lemma_sum_push(s: Seq<int>, x: int)
    ensures SumL(s.push(x)) == SumL(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x)[0] == x);
        assert(s.push(x).subrange(1, s.push(x).len() as int).len() == 0);
    } else {
        lemma_sum_push(s.subrange(1, s.len() as int), x);
    }
}

fn main() {
}

}
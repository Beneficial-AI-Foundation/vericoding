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
        SumR(s.subrange(0, s.len() as int - 1)) + s[s.len() - 1]
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
        assert(s.subrange(0, s.len() as int - 1).len() == 0);
    } else {
        // Inductive case: s.len() >= 2
        let s_without_first = s.subrange(1, s.len() as int);
        let s_without_last = s.subrange(0, s.len() as int - 1);
        let s_middle = s.subrange(1, s.len() as int - 1);
        
        // Apply induction hypothesis to subsequences
        lemma_sum_equivalence(s_without_first);
        lemma_sum_equivalence(s_without_last);
        lemma_sum_equivalence(s_middle);
        
        // Show the relationship between the subsequences
        assert(s_without_first == s_middle.push(s[s.len() - 1]));
        assert(s_without_last == seq![s[0]].add(s_middle));
        
        // Use helper lemmas
        lemma_sum_push(s_middle, s[s.len() - 1]);
        lemma_sum_prepend(s_middle, s[0]);
        
        // Now we can prove the equivalence
        assert(SumL(s) == s[0] + SumL(s_without_first));
        assert(SumL(s_without_first) == SumL(s_middle) + s[s.len() - 1]);
        assert(SumR(s) == SumR(s_without_last) + s[s.len() - 1]);
        assert(SumR(s_without_last) == s[0] + SumR(s_middle));
        
        // Since SumL(s_middle) == SumR(s_middle), we get the result
        assert(SumL(s) == s[0] + SumL(s_middle) + s[s.len() - 1]);
        assert(SumR(s) == s[0] + SumR(s_middle) + s[s.len() - 1]);
    }
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
        assert(s.push(x)[0] == s[0]);
        assert(s.push(x).subrange(1, s.push(x).len() as int) == s.subrange(1, s.len() as int).push(x));
    }
}

// Helper lemma for sequence prepend operation  
proof fn lemma_sum_prepend(s: Seq<int>, x: int)
    ensures SumR(seq![x].add(s)) == x + SumR(s)
    decreases s.len()
{
    let combined = seq![x].add(s);
    if s.len() == 0 {
        assert(combined.len() == 1);
        assert(combined[0] == x);
    } else {
        assert(combined.len() == s.len() + 1);
        assert(combined[combined.len() - 1] == s[s.len() - 1]);
        assert(combined.subrange(0, combined.len() as int - 1) == seq![x].add(s.subrange(0, s.len() as int - 1)));
        lemma_sum_prepend(s.subrange(0, s.len() as int - 1), x);
    }
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
            assert(v@.subrange(0, i as int + 1) == v@.subrange(0, i as int).push(v@[i as int]));
            lemma_sum_push(v@.subrange(0, i as int), v@[i as int]);
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

fn main() {
}

}
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

// Helper lemma for sequence push operation
proof fn lemma_sum_push(s: Seq<int>, x: int)
    ensures SumL(s.push(x)) == SumL(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        // Base case: empty sequence
        assert(s.push(x).len() == 1);
        assert(s.push(x)[0] == x);
        assert(s.push(x).subrange(1, 1) =~= seq![]);
        assert(SumL(s.push(x)) == x + SumL(seq![]));
        assert(SumL(s.push(x)) == x + 0);
        assert(SumL(s) == 0);
    } else {
        // Inductive case
        let s_tail = s.subrange(1, s.len() as int);
        let s_push = s.push(x);
        let s_push_tail = s_push.subrange(1, s_push.len() as int);
        
        assert(s_push[0] == s[0]);
        assert(s_push_tail =~= s_tail.push(x));
        
        lemma_sum_push(s_tail, x);
        
        assert(SumL(s_push) == s_push[0] + SumL(s_push_tail));
        assert(SumL(s_push) == s[0] + SumL(s_tail.push(x)));
        assert(SumL(s_push) == s[0] + SumL(s_tail) + x);
        assert(SumL(s_push) == SumL(s) + x);
    }
}

// Helper lemma for sequence prepend operation  
proof fn lemma_sum_prepend(s: Seq<int>, x: int)
    ensures SumR(seq![x].add(s)) == x + SumR(s)
    decreases s.len()
{
    let combined = seq![x].add(s);
    
    if s.len() == 0 {
        assert(combined =~= seq![x]);
        assert(combined.len() == 1);
        assert(SumR(combined) == combined[0]);
        assert(SumR(s) == 0);
    } else {
        let s_init = s.subrange(0, s.len() as int - 1);
        let combined_init = combined.subrange(0, combined.len() as int - 1);
        
        assert(combined.len() == s.len() + 1);
        assert(combined[combined.len() - 1] == s[s.len() - 1]);
        assert(combined_init =~= seq![x].add(s_init));
        
        lemma_sum_prepend(s_init, x);
        
        assert(SumR(combined) == SumR(combined_init) + combined[combined.len() - 1]);
        assert(SumR(combined) == SumR(combined_init) + s[s.len() - 1]);
        assert(SumR(combined) == (x + SumR(s_init)) + s[s.len() - 1]);
        assert(SumR(combined) == x + (SumR(s_init) + s[s.len() - 1]));
        assert(SumR(combined) == x + SumR(s));
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
        
        // Apply induction hypothesis to the middle part
        lemma_sum_equivalence(s_middle);
        
        // Establish relationships between subsequences
        assert(s_without_first.len() == s.len() - 1);
        assert(s_without_last.len() == s.len() - 1);
        assert(s_middle.len() == s.len() - 2);
        
        // Show that s_without_first = s_middle + last element
        assert(s_without_first =~= s_middle.push(s[s.len() - 1]));
        lemma_sum_push(s_middle, s[s.len() - 1]);
        assert(SumL(s_without_first) == SumL(s_middle) + s[s.len() - 1]);
        
        // Show that s_without_last = first element + s_middle  
        assert(s_without_last =~= seq![s[0]].add(s_middle));
        lemma_sum_prepend(s_middle, s[0]);
        assert(SumR(s_without_last) == s[0] + SumR(s_middle));
        
        // Now prove the main equivalence
        calc! {
            (SumL(s))
            == (s[0] + SumL(s_without_first))  // by definition of SumL
            == (s[0] + SumL(s_middle) + s[s.len() - 1])  // by lemma_sum_push
            == (s[0] + SumR(s_middle) + s[s.len() - 1])  // by induction hypothesis
            == (SumR(s_without_last) + s[s.len() - 1])  // by lemma_sum_prepend
            == (SumR(s))  // by definition of SumR
        }
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
            let current_prefix = v@.subrange(0, i as int);
            let next_prefix = v@.subrange(0, i as int + 1);
            assert(next_prefix =~= current_prefix.push(v@[i as int]));
            lemma_sum_push(current_prefix, v@[i as int]);
        }
        total = total + v[i];
        i = i + 1;
    }
    
    proof {
        assert(i == v.len());
        assert(v@.subrange(0, i as int) =~= v@);
    }
    
    total
}

fn main() {
}

}
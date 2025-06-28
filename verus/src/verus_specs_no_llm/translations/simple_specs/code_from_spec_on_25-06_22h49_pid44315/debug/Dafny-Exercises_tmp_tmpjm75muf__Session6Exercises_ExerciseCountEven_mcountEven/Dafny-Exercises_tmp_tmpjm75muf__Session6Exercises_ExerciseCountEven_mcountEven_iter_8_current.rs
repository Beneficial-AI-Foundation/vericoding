use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn CountEven(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let first = s[0];
        let rest_count = CountEven(s.subrange(1, s.len() as int));
        if first % 2 == 0 {
            rest_count + 1
        } else {
            rest_count
        }
    }
}

// Simplified lemma that directly proves what we need for the loop
proof fn lemma_count_even_one_step(s: Seq<int>, k: int)
    requires
        0 <= k < s.len()
    ensures
        CountEven(s.subrange(0, k + 1)) == CountEven(s.subrange(0, k)) + (if s[k] % 2 == 0 { 1 } else { 0 })
    decreases k
{
    if k == 0 {
        // Base case: CountEven(s[0..1]) vs CountEven(s[0..0]) 
        let empty_seq = s.subrange(0, 0);
        let one_elem = s.subrange(0, 1);
        assert(empty_seq.len() == 0);
        assert(CountEven(empty_seq) == 0);
        assert(one_elem.len() == 1);
        assert(one_elem[0] == s[0]);
        // By definition of CountEven on one_elem:
        // CountEven(one_elem) = CountEven(one_elem.subrange(1,1)) + (if s[0] % 2 == 0 { 1 } else { 0 })
        //                     = 0 + (if s[0] % 2 == 0 { 1 } else { 0 })
        assert(one_elem.subrange(1, 1).len() == 0);
    } else {
        // Recursive case: use the definition of CountEven
        lemma_count_even_one_step(s, k - 1);
        
        let s_k = s.subrange(0, k);
        let s_k_plus_1 = s.subrange(0, k + 1);
        
        // Both sequences start with the same element s[0]
        assert(s_k_plus_1[0] == s[0]);
        assert(s_k[0] == s[0]);
        
        // The "rest" parts differ by one element
        let rest_k = s_k.subrange(1, s_k.len() as int);
        let rest_k_plus_1 = s_k_plus_1.subrange(1, s_k_plus_1.len() as int);
        
        assert(rest_k == s.subrange(1, k));
        assert(rest_k_plus_1 == s.subrange(1, k + 1));
        
        // Apply induction to the suffix
        lemma_count_even_one_step(s.subrange(1, s.len() as int), k - 1);
        
        // Now we can conclude using the definition of CountEven
        assert(CountEven(s_k_plus_1) == CountEven(rest_k_plus_1) + (if s[0] % 2 == 0 { 1 } else { 0 }));
        assert(CountEven(s_k) == CountEven(rest_k) + (if s[0] % 2 == 0 { 1 } else { 0 }));
        assert(CountEven(rest_k_plus_1) == CountEven(rest_k) + (if s[k] % 2 == 0 { 1 } else { 0 }));
    }
}

fn mcountEven(v: Vec<int>) -> (n: int)
    requires
        positive(v@)
    ensures
        n == CountEven(v@)
{
    let mut count = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            count == CountEven(v@.subrange(0, i as int)),
            positive(v@)
    {
        proof {
            lemma_count_even_one_step(v@, i as int);
        }
        
        if v[i] % 2 == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == v.len());
        assert(v@.subrange(0, v.len() as int) == v@);
    }
    
    count
}

}
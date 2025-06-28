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

// Helper lemma for empty sequence
proof fn lemma_count_even_empty(s: Seq<int>)
    ensures
        CountEven(s.subrange(0, 0)) == 0
{
    assert(s.subrange(0, 0).len() == 0);
}

// Key lemma: extending a sequence by one element
proof fn lemma_count_even_extend(s: Seq<int>, k: int)
    requires
        0 <= k < s.len()
    ensures
        CountEven(s.subrange(0, k + 1)) == CountEven(s.subrange(0, k)) + (if s[k] % 2 == 0 { 1 } else { 0 })
    decreases k
{
    if k == 0 {
        // Base case: s.subrange(0, 1) vs s.subrange(0, 0)
        let empty = s.subrange(0, 0);
        let single = s.subrange(0, 1);
        
        assert(empty.len() == 0);
        assert(CountEven(empty) == 0);
        
        assert(single.len() == 1);
        assert(single[0] == s[0]);
        
        // By definition of CountEven on single element sequence
        let rest = single.subrange(1, 1);
        assert(rest.len() == 0);
        assert(CountEven(rest) == 0);
        
        // Therefore CountEven(single) = CountEven(rest) + (if single[0] % 2 == 0 { 1 } else { 0 })
        //                              = 0 + (if s[0] % 2 == 0 { 1 } else { 0 })
        //                              = (if s[0] % 2 == 0 { 1 } else { 0 })
        //                              = CountEven(empty) + (if s[0] % 2 == 0 { 1 } else { 0 })
    } else {
        // Inductive case: assume the property holds for k-1
        lemma_count_even_extend(s, k - 1);
        
        let s_k = s.subrange(0, k);
        let s_k_plus_1 = s.subrange(0, k + 1);
        
        // We need to show: CountEven(s_k_plus_1) = CountEven(s_k) + (if s[k] % 2 == 0 { 1 } else { 0 })
        
        // By definition of CountEven on s_k_plus_1:
        // CountEven(s_k_plus_1) = CountEven(s_k_plus_1.subrange(1, k+1)) + (if s_k_plus_1[0] % 2 == 0 { 1 } else { 0 })
        //                       = CountEven(s.subrange(1, k+1)) + (if s[0] % 2 == 0 { 1 } else { 0 })
        
        // By definition of CountEven on s_k:
        // CountEven(s_k) = CountEven(s_k.subrange(1, k)) + (if s_k[0] % 2 == 0 { 1 } else { 0 })
        //                = CountEven(s.subrange(1, k)) + (if s[0] % 2 == 0 { 1 } else { 0 })
        
        // Now we need to relate CountEven(s.subrange(1, k+1)) to CountEven(s.subrange(1, k))
        let s_suffix = s.subrange(1, s.len() as int);
        lemma_count_even_extend(s_suffix, k - 1);
        
        // This gives us: CountEven(s_suffix.subrange(0, k)) = CountEven(s_suffix.subrange(0, k-1)) + (if s_suffix[k-1] % 2 == 0 { 1 } else { 0 })
        // Which translates to: CountEven(s.subrange(1, k+1)) = CountEven(s.subrange(1, k)) + (if s[k] % 2 == 0 { 1 } else { 0 })
        
        assert(s.subrange(1, k + 1) == s_suffix.subrange(0, k));
        assert(s.subrange(1, k) == s_suffix.subrange(0, k - 1));
        assert(s_suffix[k - 1] == s[k]);
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
    
    proof {
        lemma_count_even_empty(v@);
    }
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            count == CountEven(v@.subrange(0, i as int)),
            positive(v@)
    {
        proof {
            lemma_count_even_extend(v@, i as int);
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
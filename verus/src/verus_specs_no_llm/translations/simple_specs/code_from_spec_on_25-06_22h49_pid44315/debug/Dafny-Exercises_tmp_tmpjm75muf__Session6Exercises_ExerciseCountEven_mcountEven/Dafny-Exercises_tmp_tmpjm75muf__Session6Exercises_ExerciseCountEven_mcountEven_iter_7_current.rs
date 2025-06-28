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

// Helper lemma to prove the relationship between CountEven and subranges
proof fn lemma_count_even_extend(s: Seq<int>, i: int)
    requires
        0 <= i < s.len()
    ensures
        CountEven(s.subrange(0, i + 1)) == CountEven(s.subrange(0, i)) + (if s[i] % 2 == 0 { 1 } else { 0 })
    decreases i
{
    if i == 0 {
        // Base case: extending from empty sequence to sequence of length 1
        let sub_0 = s.subrange(0, 0);
        let sub_1 = s.subrange(0, 1);
        assert(sub_0.len() == 0);
        assert(CountEven(sub_0) == 0);
        assert(sub_1.len() == 1);
        assert(sub_1[0] == s[0]);
        // CountEven(sub_1) = CountEven(sub_1.subrange(1,1)) + (if s[0] % 2 == 0 { 1 } else { 0 })
        //                 = 0 + (if s[0] % 2 == 0 { 1 } else { 0 })
        assert(sub_1.subrange(1, 1).len() == 0);
        assert(CountEven(sub_1.subrange(1, 1)) == 0);
    } else {
        // Inductive case
        lemma_count_even_extend(s, i - 1);
        
        let sub_i = s.subrange(0, i);
        let sub_i_plus_1 = s.subrange(0, i + 1);
        
        assert(sub_i_plus_1.len() > 0);
        assert(sub_i_plus_1[0] == s[0]);
        
        let rest_i_plus_1 = sub_i_plus_1.subrange(1, sub_i_plus_1.len() as int);
        let rest_i = sub_i.subrange(1, sub_i.len() as int);
        
        assert(rest_i_plus_1 == s.subrange(1, i + 1));
        assert(rest_i == s.subrange(1, i));
        
        // Apply induction hypothesis to the suffix starting at position 1
        if i > 1 {
            lemma_count_even_extend(s.subrange(1, s.len() as int), i - 1);
        }
        
        // The key insight: rest_i_plus_1 extends rest_i by one element at position i
        assert(rest_i_plus_1 == rest_i.push(s[i]));
        assert(CountEven(rest_i_plus_1) == CountEven(rest_i) + (if s[i] % 2 == 0 { 1 } else { 0 }));
        
        // Now apply the definition of CountEven
        assert(CountEven(sub_i_plus_1) == CountEven(rest_i_plus_1) + (if s[0] % 2 == 0 { 1 } else { 0 }));
        assert(CountEven(sub_i) == CountEven(rest_i) + (if s[0] % 2 == 0 { 1 } else { 0 }));
    }
}

// Simpler helper lemma that directly matches our use case
proof fn lemma_count_even_step(s: Seq<int>, i: int)
    requires
        0 <= i < s.len()
    ensures
        CountEven(s.subrange(0, i + 1)) == CountEven(s.subrange(0, i)) + (if s[i] % 2 == 0 { 1 } else { 0 })
{
    let s_i = s.subrange(0, i);
    let s_i_plus_1 = s.subrange(0, i + 1);
    
    if i == 0 {
        assert(s_i.len() == 0);
        assert(CountEven(s_i) == 0);
        assert(s_i_plus_1.len() == 1);
        assert(s_i_plus_1[0] == s[0]);
    } else {
        // Use the recursive structure more directly
        assert(s_i_plus_1 == s_i.push(s[i]));
        
        // Key insight: we can relate CountEven on extended sequence
        // by using the definition directly
        if s_i_plus_1.len() > 0 {
            let first = s_i_plus_1[0];
            let rest = s_i_plus_1.subrange(1, s_i_plus_1.len() as int);
            assert(first == s[0]);
            assert(rest == s.subrange(1, i + 1));
            
            // Apply the same reasoning to s_i
            if s_i.len() > 0 {
                let first_i = s_i[0];
                let rest_i = s_i.subrange(1, s_i.len() as int);
                assert(first_i == s[0]);
                assert(rest_i == s.subrange(1, i));
                
                // The key step: rest extends rest_i by one element
                lemma_count_even_step(s.subrange(1, s.len() as int), i - 1);
            }
        }
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
            lemma_count_even_step(v@, i as int);
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
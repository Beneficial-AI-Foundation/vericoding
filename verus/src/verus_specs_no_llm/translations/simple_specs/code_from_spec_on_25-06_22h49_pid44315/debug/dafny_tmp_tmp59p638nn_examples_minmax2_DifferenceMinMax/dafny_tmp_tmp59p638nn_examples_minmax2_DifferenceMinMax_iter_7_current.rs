use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Max(s: Seq<int>) -> int
    requires s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_max = Max(s.subrange(1, s.len() as int));
        if s[0] >= rest_max { s[0] } else { rest_max }
    }
}

spec fn Min(s: Seq<int>) -> int
    requires s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_min = Min(s.subrange(1, s.len() as int));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}

proof fn lemma_max_in_range(s: Seq<int>, i: int)
    requires 
        s.len() > 0,
        0 <= i < s.len()
    ensures
        Max(s) >= s[i]
    decreases s.len()
{
    if s.len() == 1 {
        assert(i == 0);
        assert(Max(s) == s[0]);
    } else {
        let rest = s.subrange(1, s.len() as int);
        if i == 0 {
            // Max(s) is either s[0] or Max(rest), both >= s[0]
        } else {
            // s[i] is in the rest
            assert(s[i] == rest[i - 1]);
            lemma_max_in_range(rest, i - 1);
            assert(Max(rest) >= s[i]);
            // Max(s) is either s[0] or Max(rest), both >= Max(rest) >= s[i]
        }
    }
}

proof fn lemma_min_in_range(s: Seq<int>, i: int)
    requires 
        s.len() > 0,
        0 <= i < s.len()
    ensures
        Min(s) <= s[i]
    decreases s.len()
{
    if s.len() == 1 {
        assert(i == 0);
        assert(Min(s) == s[0]);
    } else {
        let rest = s.subrange(1, s.len() as int);
        if i == 0 {
            // Min(s) is either s[0] or Min(rest), both <= s[0]
        } else {
            // s[i] is in the rest
            assert(s[i] == rest[i - 1]);
            lemma_min_in_range(rest, i - 1);
            assert(Min(rest) <= s[i]);
            // Min(s) is either s[0] or Min(rest), both <= Min(rest) <= s[i]
        }
    }
}

proof fn lemma_max_exists(s: Seq<int>) -> (idx: int)
    requires s.len() > 0
    ensures 
        0 <= idx < s.len(),
        Max(s) == s[idx]
    decreases s.len()
{
    if s.len() == 1 {
        0
    } else {
        let rest = s.subrange(1, s.len() as int);
        let rest_idx = lemma_max_exists(rest);
        if s[0] >= Max(rest) {
            0
        } else {
            rest_idx + 1
        }
    }
}

proof fn lemma_min_exists(s: Seq<int>) -> (idx: int)
    requires s.len() > 0
    ensures 
        0 <= idx < s.len(),
        Min(s) == s[idx]
    decreases s.len()
{
    if s.len() == 1 {
        0
    } else {
        let rest = s.subrange(1, s.len() as int);
        let rest_idx = lemma_min_exists(rest);
        if s[0] <= Min(rest) {
            0
        } else {
            rest_idx + 1
        }
    }
}

proof fn lemma_max_prefix_property(s: Seq<int>, i: int)
    requires
        s.len() > 0,
        0 < i < s.len()
    ensures
        Max(s.subrange(0, (i + 1) as int)) == 
            if s[i] > Max(s.subrange(0, i as int)) { 
                s[i] 
            } else { 
                Max(s.subrange(0, i as int)) 
            }
{
    let prefix_i = s.subrange(0, i as int);
    let prefix_i_plus_1 = s.subrange(0, (i + 1) as int);
    
    // Establish the relationship between the two prefixes
    assert(prefix_i_plus_1.len() == prefix_i.len() + 1);
    assert forall |j: int| 0 <= j < i ==> prefix_i_plus_1[j] == prefix_i[j];
    assert(prefix_i_plus_1[i] == s[i]);
    
    // The key insight: prefix_i_plus_1 is exactly prefix_i with s[i] appended
    // So Max(prefix_i_plus_1) follows the recursive definition
    assert(prefix_i_plus_1 =~= seq![s[0]].add(s.subrange(1, (i + 1) as int)));
    
    let max_i = Max(prefix_i);
    
    // Use the recursive definition to establish the relationship
    if s[i] > max_i {
        // Prove that s[i] is greater than all elements in prefix_i
        assert forall |j: int| 0 <= j < i ==> s[i] > prefix_i[j] by {
            lemma_max_in_range(prefix_i, j);
            assert(max_i >= prefix_i[j]);
        };
    } else {
        // Prove that max_i is still the maximum
        let max_idx = lemma_max_exists(prefix_i);
        assert(prefix_i_plus_1[max_idx] == max_i);
        lemma_max_in_range(prefix_i_plus_1, max_idx);
    }
}

proof fn lemma_min_prefix_property(s: Seq<int>, i: int)
    requires
        s.len() > 0,
        0 < i < s.len()
    ensures
        Min(s.subrange(0, (i + 1) as int)) == 
            if s[i] < Min(s.subrange(0, i as int)) { 
                s[i] 
            } else { 
                Min(s.subrange(0, i as int)) 
            }
{
    let prefix_i = s.subrange(0, i as int);
    let prefix_i_plus_1 = s.subrange(0, (i + 1) as int);
    
    // Establish the relationship between the two prefixes
    assert(prefix_i_plus_1.len() == prefix_i.len() + 1);
    assert forall |j: int| 0 <= j < i ==> prefix_i_plus_1[j] == prefix_i[j];
    assert(prefix_i_plus_1[i] == s[i]);
    
    let min_i = Min(prefix_i);
    
    // Use the recursive definition to establish the relationship
    if s[i] < min_i {
        // Prove that s[i] is smaller than all elements in prefix_i
        assert forall |j: int| 0 <= j < i ==> s[i] < prefix_i[j] by {
            lemma_min_in_range(prefix_i, j);
            assert(min_i <= prefix_i[j]);
        };
    } else {
        // Prove that min_i is still the minimum
        let min_idx = lemma_min_exists(prefix_i);
        assert(prefix_i_plus_1[min_idx] == min_i);
        lemma_min_in_range(prefix_i_plus_1, min_idx);
    }
}

fn DifferenceMinMax(a: Vec<int>) -> (diff: int)
    requires
        a.len() > 0
    ensures
        diff == (Max(a@) - Min(a@))
{
    let mut max_val = a[0];
    let mut min_val = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max_val == Max(a@.subrange(0, i as int)),
            min_val == Min(a@.subrange(0, i as int))
    {
        proof {
            if i < a.len() {
                lemma_max_prefix_property(a@, i as int);
                lemma_min_prefix_property(a@, i as int);
            }
        }
        
        if a[i] > max_val {
            max_val = a[i];
        }
        if a[i] < min_val {
            min_val = a[i];
        }
        i += 1;
    }
    
    // At the end, i == a.len(), so we have the full sequence
    assert(a@.subrange(0, i as int) =~= a@);
    
    max_val - min_val
}

}
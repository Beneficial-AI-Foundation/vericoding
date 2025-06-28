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
        assert(Max(rest) == rest[rest_idx]);
        assert(rest[rest_idx] == s[rest_idx + 1]);
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
        assert(Min(rest) == rest[rest_idx]);
        assert(rest[rest_idx] == s[rest_idx + 1]);
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
    
    // Key insight: prefix_i_plus_1 can be viewed as prefix_i with s[i] as the first element
    // and prefix_i.subrange(1, prefix_i.len()) as the rest
    assert(prefix_i_plus_1.len() == i + 1);
    assert(prefix_i.len() == i);
    assert(prefix_i_plus_1[i] == s[i]);
    
    // Since prefix_i_plus_1 has length > 1, use recursive definition
    let rest = prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int);
    assert(rest =~= prefix_i);
    
    // By definition of Max for sequences of length > 1:
    // Max(prefix_i_plus_1) = if prefix_i_plus_1[0] >= Max(rest) then prefix_i_plus_1[0] else Max(rest)
    // Since prefix_i_plus_1[0] = s[0] and Max(rest) = Max(prefix_i), we need to relate this
    // to what we want to prove
    
    // We need to show the relationship holds by the structure of the sequence
    if s[i] > Max(prefix_i) {
        // Need to show that Max(prefix_i_plus_1) == s[i]
        // Since s[i] > Max(prefix_i), and all elements in prefix_i are <= Max(prefix_i)
        assert forall |j: int| 0 <= j < i ==> s[i] > prefix_i[j] by {
            lemma_max_in_range(prefix_i, j);
        }
        // Therefore s[i] is the maximum in prefix_i_plus_1
    } else {
        // s[i] <= Max(prefix_i), so Max(prefix_i) should still be the maximum
        let max_idx = lemma_max_exists(prefix_i);
        assert(prefix_i_plus_1[max_idx] == Max(prefix_i));
        // Since s[i] <= Max(prefix_i), Max(prefix_i) is still the maximum
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
    
    assert(prefix_i_plus_1.len() == i + 1);
    assert(prefix_i.len() == i);
    assert(prefix_i_plus_1[i] == s[i]);
    
    if s[i] < Min(prefix_i) {
        // Need to show that Min(prefix_i_plus_1) == s[i]
        assert forall |j: int| 0 <= j < i ==> s[i] < prefix_i[j] by {
            lemma_min_in_range(prefix_i, j);
        }
    } else {
        // s[i] >= Min(prefix_i), so Min(prefix_i) should still be the minimum
        let min_idx = lemma_min_exists(prefix_i);
        assert(prefix_i_plus_1[min_idx] == Min(prefix_i));
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
    
    // Base case: when i == 1, we have processed the first element
    assert(a@.subrange(0, 1) == seq![a[0]]);
    assert(Max(a@.subrange(0, 1)) == a[0]);
    assert(Min(a@.subrange(0, 1)) == a[0]);
    
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
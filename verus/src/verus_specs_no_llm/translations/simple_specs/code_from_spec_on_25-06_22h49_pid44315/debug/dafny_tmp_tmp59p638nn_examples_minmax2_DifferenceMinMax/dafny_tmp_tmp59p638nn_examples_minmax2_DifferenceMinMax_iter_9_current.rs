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
    decreases s.len() - i
{
    let prefix_i = s.subrange(0, i as int);
    let prefix_i_plus_1 = s.subrange(0, (i + 1) as int);
    
    // Establish basic properties
    assert(prefix_i_plus_1.len() == i + 1);
    assert(prefix_i.len() == i);
    assert(prefix_i_plus_1[i] == s[i]);
    
    // Show that prefix_i_plus_1 contains all elements of prefix_i plus s[i]
    assert forall |j: int| 0 <= j < i ==> prefix_i_plus_1[j] == prefix_i[j];
    
    if s[i] > Max(prefix_i) {
        // s[i] is greater than all elements in prefix_i
        assert forall |j: int| 0 <= j < i ==> s[i] > prefix_i[j] by {
            lemma_max_in_range(prefix_i, j);
            assert(prefix_i[j] <= Max(prefix_i));
        }
        
        // Therefore s[i] is the maximum in prefix_i_plus_1
        assert forall |j: int| 0 <= j < prefix_i_plus_1.len() ==> prefix_i_plus_1[j] <= s[i] by {
            if j < i {
                assert(prefix_i_plus_1[j] == prefix_i[j]);
            } else {
                assert(j == i);
                assert(prefix_i_plus_1[j] == s[i]);
            }
        }
        
        // Use the fact that Max returns the maximum value
        lemma_max_in_range(prefix_i_plus_1, i as int);
        assert(Max(prefix_i_plus_1) >= s[i]);
        
        // Prove the other direction: Max(prefix_i_plus_1) <= s[i]
        let max_idx = lemma_max_exists(prefix_i_plus_1);
        assert(Max(prefix_i_plus_1) == prefix_i_plus_1[max_idx]);
        // From our assertion above, prefix_i_plus_1[max_idx] <= s[i]
        
    } else {
        // s[i] <= Max(prefix_i)
        let max_idx = lemma_max_exists(prefix_i);
        assert(Max(prefix_i) == prefix_i[max_idx]);
        assert(prefix_i_plus_1[max_idx] == Max(prefix_i));
        
        // Show Max(prefix_i) is still the maximum in prefix_i_plus_1
        assert forall |j: int| 0 <= j < prefix_i_plus_1.len() ==> prefix_i_plus_1[j] <= Max(prefix_i) by {
            if j < i {
                assert(prefix_i_plus_1[j] == prefix_i[j]);
                lemma_max_in_range(prefix_i, j);
            } else {
                assert(j == i);
                assert(prefix_i_plus_1[j] == s[i]);
            }
        }
        
        lemma_max_in_range(prefix_i_plus_1, max_idx);
        let max_idx_new = lemma_max_exists(prefix_i_plus_1);
        assert(Max(prefix_i_plus_1) == prefix_i_plus_1[max_idx_new]);
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
    decreases s.len() - i
{
    let prefix_i = s.subrange(0, i as int);
    let prefix_i_plus_1 = s.subrange(0, (i + 1) as int);
    
    assert(prefix_i_plus_1.len() == i + 1);
    assert(prefix_i.len() == i);
    assert(prefix_i_plus_1[i] == s[i]);
    
    assert forall |j: int| 0 <= j < i ==> prefix_i_plus_1[j] == prefix_i[j];
    
    if s[i] < Min(prefix_i) {
        // s[i] is smaller than all elements in prefix_i
        assert forall |j: int| 0 <= j < i ==> s[i] < prefix_i[j] by {
            lemma_min_in_range(prefix_i, j);
            assert(prefix_i[j] >= Min(prefix_i));
        }
        
        // Therefore s[i] is the minimum in prefix_i_plus_1
        assert forall |j: int| 0 <= j < prefix_i_plus_1.len() ==> prefix_i_plus_1[j] >= s[i] by {
            if j < i {
                assert(prefix_i_plus_1[j] == prefix_i[j]);
            } else {
                assert(j == i);
                assert(prefix_i_plus_1[j] == s[i]);
            }
        }
        
        lemma_min_in_range(prefix_i_plus_1, i as int);
        assert(Min(prefix_i_plus_1) <= s[i]);
        
        let min_idx = lemma_min_exists(prefix_i_plus_1);
        assert(Min(prefix_i_plus_1) == prefix_i_plus_1[min_idx]);
        
    } else {
        // s[i] >= Min(prefix_i)
        let min_idx = lemma_min_exists(prefix_i);
        assert(Min(prefix_i) == prefix_i[min_idx]);
        assert(prefix_i_plus_1[min_idx] == Min(prefix_i));
        
        assert forall |j: int| 0 <= j < prefix_i_plus_1.len() ==> prefix_i_plus_1[j] >= Min(prefix_i) by {
            if j < i {
                assert(prefix_i_plus_1[j] == prefix_i[j]);
                lemma_min_in_range(prefix_i, j);
            } else {
                assert(j == i);
                assert(prefix_i_plus_1[j] == s[i]);
            }
        }
        
        lemma_min_in_range(prefix_i_plus_1, min_idx);
        let min_idx_new = lemma_min_exists(prefix_i_plus_1);
        assert(Min(prefix_i_plus_1) == prefix_i_plus_1[min_idx_new]);
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
        if a[i] > max_val {
            proof {
                lemma_max_prefix_property(a@, i as int);
            }
            max_val = a[i];
        } else {
            proof {
                lemma_max_prefix_property(a@, i as int);
            }
        }
        
        if a[i] < min_val {
            proof {
                lemma_min_prefix_property(a@, i as int);
            }
            min_val = a[i];
        } else {
            proof {
                lemma_min_prefix_property(a@, i as int);
            }
        }
        
        i += 1;
    }
    
    // At the end, i == a.len(), so we have the full sequence
    assert(a@.subrange(0, i as int) =~= a@);
    
    max_val - min_val
}

}
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
    
    // Establish basic properties
    assert(prefix_i_plus_1.len() == i + 1);
    assert(prefix_i.len() == i);
    assert(prefix_i_plus_1[i] == s[i]);
    
    // Use recursive definition of Max
    assert(Max(prefix_i_plus_1) == 
        if prefix_i_plus_1[0] >= Max(prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int)) {
            prefix_i_plus_1[0]
        } else {
            Max(prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int))
        });
    
    // The subrange from 1 to end is the same as prefix_i
    assert(prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int) =~= prefix_i);
    assert(prefix_i_plus_1[0] == s[0]);
    
    // We need to relate this to the tail starting from position i
    // Let's use a simpler approach based on the recursive structure
    if prefix_i_plus_1.len() == 1 {
        assert(i == 0);
        assert(Max(prefix_i_plus_1) == s[i]);
    } else {
        let tail = prefix_i_plus_1.subrange(1, prefix_i_plus_1.len() as int);
        assert(tail =~= prefix_i);
        
        if s[i] > Max(prefix_i) {
            // Need to show Max(prefix_i_plus_1) == s[i]
            // This requires more complex reasoning about the recursive structure
        } else {
            // Need to show Max(prefix_i_plus_1) == Max(prefix_i)  
        }
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
    
    // Similar structure to max case but for min
    if prefix_i_plus_1.len() == 1 {
        assert(i == 0);
        assert(Min(prefix_i_plus_1) == s[i]);
    }
}

// Simpler helper lemmas for the specific case we need
proof fn lemma_max_with_new_element(s: Seq<int>, new_elem: int)
    requires s.len() > 0
    ensures 
        Max(s.push(new_elem)) == if new_elem > Max(s) { new_elem } else { Max(s) }
{
    let extended = s.push(new_elem);
    if new_elem > Max(s) {
        // Show that new_elem is the maximum
        assert forall |i: int| 0 <= i < extended.len() ==> extended[i] <= new_elem by {
            if i < s.len() {
                assert(extended[i] == s[i]);
                lemma_max_in_range(s, i);
                assert(s[i] <= Max(s));
                assert(Max(s) < new_elem);
            } else {
                assert(i == s.len());
                assert(extended[i] == new_elem);
            }
        }
    } else {
        // Show that Max(s) is still the maximum
        assert forall |i: int| 0 <= i < extended.len() ==> extended[i] <= Max(s) by {
            if i < s.len() {
                assert(extended[i] == s[i]);
                lemma_max_in_range(s, i);
            } else {
                assert(i == s.len());
                assert(extended[i] == new_elem);
            }
        }
    }
}

proof fn lemma_min_with_new_element(s: Seq<int>, new_elem: int)
    requires s.len() > 0
    ensures 
        Min(s.push(new_elem)) == if new_elem < Min(s) { new_elem } else { Min(s) }
{
    let extended = s.push(new_elem);
    if new_elem < Min(s) {
        // Show that new_elem is the minimum
        assert forall |i: int| 0 <= i < extended.len() ==> extended[i] >= new_elem by {
            if i < s.len() {
                assert(extended[i] == s[i]);
                lemma_min_in_range(s, i);
                assert(s[i] >= Min(s));
                assert(Min(s) > new_elem);
            } else {
                assert(i == s.len());
                assert(extended[i] == new_elem);
            }
        }
    } else {
        // Show that Min(s) is still the minimum
        assert forall |i: int| 0 <= i < extended.len() ==> extended[i] >= Min(s) by {
            if i < s.len() {
                assert(extended[i] == s[i]);
                lemma_min_in_range(s, i);
            } else {
                assert(i == s.len());
                assert(extended[i] == new_elem);
            }
        }
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
        let old_i = i;
        
        // Get current prefix
        let current_prefix = a@.subrange(0, i as int);
        let next_prefix = a@.subrange(0, (i + 1) as int);
        
        // Key insight: next_prefix is current_prefix with a[i] appended
        assert(next_prefix =~= current_prefix.push(a[i as int]));
        
        proof {
            lemma_max_with_new_element(current_prefix, a[i as int]);
            lemma_min_with_new_element(current_prefix, a[i as int]);
        }
        
        if a[i] > max_val {
            max_val = a[i];
        }
        
        if a[i] < min_val {
            min_val = a[i];
        }
        
        i += 1;
        
        // Verify the invariant holds
        assert(Max(a@.subrange(0, i as int)) == max_val);
        assert(Min(a@.subrange(0, i as int)) == min_val);
    }
    
    // At the end, i == a.len(), so we have the full sequence
    assert(a@.subrange(0, i as int) =~= a@);
    
    max_val - min_val
}

}
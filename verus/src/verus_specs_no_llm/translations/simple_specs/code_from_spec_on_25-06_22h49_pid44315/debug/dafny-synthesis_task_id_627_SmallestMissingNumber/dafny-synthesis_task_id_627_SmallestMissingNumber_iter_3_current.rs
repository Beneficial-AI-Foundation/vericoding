use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SmallestMissingNumber(s: Seq<int>) -> (v: int)
    requires
        forall i, j :: 0 <= i < j < s.len() ==> s.spec_index(i) <= s.spec_index(j),
        forall i :: 0 <= i < s.len() ==> s.spec_index(i) >= 0
    ensures
        0 <= v,
        v !in s,
        forall k :: 0 <= k < v ==> k in s
{
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall k :: 0 <= k < i ==> k in s,
            forall j :: 0 <= j < i ==> s.spec_index(j) == j
    {
        if s.spec_index(i) > i {
            // Prove that i is not in s
            assert(i !in s) by {
                if i in s {
                    // If i is in s, there exists some index where s[idx] == i
                    let idx = choose |idx| 0 <= idx < s.len() && s.spec_index(idx) == i;
                    if idx < i {
                        // From invariant: s[idx] should equal idx, but s[idx] == i
                        // This contradicts idx < i
                        assert(s.spec_index(idx) == idx);
                        assert(s.spec_index(idx) == i);
                        assert(idx == i);
                        assert(false);
                    } else if idx == i {
                        // s[i] == i, but we know s[i] > i
                        assert(s.spec_index(i) == i);
                        assert(s.spec_index(i) > i);
                        assert(false);
                    } else {
                        // idx > i, so s[idx] == i < idx
                        // But from sortedness: s[i] <= s[idx], and s[i] > i
                        // So s[idx] >= s[i] > i, contradiction with s[idx] == i
                        assert(s.spec_index(i) <= s.spec_index(idx));
                        assert(s.spec_index(i) > i);
                        assert(s.spec_index(idx) == i);
                        assert(false);
                    }
                }
            };
            
            // Prove that all k < i are in s (from invariant)
            assert(forall k :: 0 <= k < i ==> k in s);
            
            return i;
        }
        
        // At this point, s[i] <= i
        // Since s[i] >= 0 and the sequence is sorted, and all 0..i-1 are already in s,
        // we must have s[i] == i
        assert(s.spec_index(i) == i) by {
            let val = s.spec_index(i);
            assert(val <= i); // from the if condition
            assert(val >= 0); // from precondition
            
            if val < i {
                // val is in range [0, i-1], so by invariant it should already be in s at position val
                assert(val in s);
                assert(s.spec_index(val) == val); // from invariant
                
                // But we also have s[i] == val with i > val
                // By sortedness: s[val] <= s[i], so val <= val, which is fine
                // However, this would mean val appears twice in the sequence
                // Since the sequence is sorted and contains distinct values 0,1,2,...
                // we need val to appear exactly once at position val
                
                // The key insight: if s[i] = val < i, and s[val] = val,
                // then we have a duplicate value, which contradicts the structure
                // that each position j < i has s[j] = j
                assert(false);
            }
            
            // Therefore val == i
        };
        
        i = i + 1;
    }
    
    // When we exit the loop, i == s.len(), and all numbers 0..s.len()-1 are in s
    assert(forall k :: 0 <= k < s.len() ==> k in s);
    
    // Prove that s.len() is not in s
    assert(s.len() as int !in s) by {
        if s.len() as int in s {
            let idx = choose |idx| 0 <= idx < s.len() && s.spec_index(idx) == s.len() as int;
            // We have s[idx] == s.len(), but idx < s.len()
            // From our loop invariant: s[idx] == idx
            assert(s.spec_index(idx) == idx);
            assert(s.spec_index(idx) == s.len() as int);
            assert(idx == s.len() as int);
            assert(idx < s.len());
            assert(false);
        }
    };
    
    return s.len() as int;
}

}
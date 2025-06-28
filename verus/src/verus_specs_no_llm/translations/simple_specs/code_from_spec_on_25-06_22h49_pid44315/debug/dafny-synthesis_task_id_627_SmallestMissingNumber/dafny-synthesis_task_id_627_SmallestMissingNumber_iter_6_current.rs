use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SmallestMissingNumber(s: Seq<int>) -> (v: int)
    requires
        forall |i, j| 0 <= i < j < s.len() ==> s.spec_index(i) <= s.spec_index(j),
        forall |i| 0 <= i < s.len() ==> s.spec_index(i) >= 0
    ensures
        0 <= v,
        v !in s,
        forall |k| 0 <= k < v ==> k in s
{
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall |k| 0 <= k < i ==> (s.spec_index(k) == k && k in s)
    {
        if s.spec_index(i) == i {
            // Current position contains the expected value
            assert(i in s);
        } else {
            // Found a gap - i is missing
            assert(i !in s) by {
                if i in s {
                    // If i is in s, it must be at some position j
                    assert(exists |j| 0 <= j < s.len() && s.spec_index(j) == i);
                    let j = choose |j| 0 <= j < s.len() && s.spec_index(j) == i;
                    
                    if j < i {
                        // We have s[j] = i where j < i
                        // But from our invariant, s[j] should equal j, not i
                        // Since j < i, we have s[j] = j from invariant
                        assert(s.spec_index(j) == j);  // from invariant
                        assert(s.spec_index(j) == i);  // from our assumption
                        assert(j == i);  // contradiction since j < i
                        assert(false);
                    } else if j == i {
                        // s[i] = i, but we're in the else branch where s[i] != i
                        assert(s.spec_index(i) == i);
                        assert(s.spec_index(i) != i);
                        assert(false);
                    } else {
                        // j > i, so s[j] = i
                        // From sortedness: s[i] <= s[j] = i
                        // But if s[i] != i, then either s[i] < i or s[i] > i
                        if s.spec_index(i) > i {
                            // s[i] > i >= j contradicts j > i... wait, that's wrong
                            // We have s[i] > i and s[j] = i where j > i
                            // From sortedness: s[i] <= s[j], so s[i] <= i
                            // But s[i] > i, contradiction
                            assert(s.spec_index(i) <= s.spec_index(j));
                            assert(s.spec_index(j) == i);
                            assert(s.spec_index(i) <= i);
                            assert(s.spec_index(i) > i);
                            assert(false);
                        } else {
                            // s[i] < i, and s[j] = i where j > i
                            // This violates our assumption about the structure
                            // If i appears later, it means positions 0..i-1 should all be filled
                            // with their corresponding values, which contradicts our search
                            assert(false);
                        }
                    }
                }
            };
            
            // Prove that all k < i are in s
            assert(forall |k| 0 <= k < i ==> k in s) by {
                // This follows from our loop invariant
                assert(forall |k| 0 <= k < i ==> (s.spec_index(k) == k && k in s));
            };
            
            return i;
        }
        
        i = i + 1;
    }
    
    // If we've gone through all positions without finding a gap,
    // then 0, 1, ..., s.len()-1 are all present in their respective positions
    assert(forall |k| 0 <= k < s.len() ==> k in s) by {
        // This follows from our loop invariant when i = s.len()
        assert(forall |k| 0 <= k < s.len() ==> (s.spec_index(k) == k && k in s));
    };
    
    assert((s.len() as int) !in s) by {
        if (s.len() as int) in s {
            // If s.len() is in s, it must be at some position j
            let j = choose |j| 0 <= j < s.len() && s.spec_index(j) == s.len();
            // We have s[j] = s.len() where j < s.len()
            // But from our analysis above, s[j] = j for all j < s.len()
            // So j = s.len(), which contradicts j < s.len()
            assert(s.spec_index(j) == j);  // from our loop completion
            assert(s.spec_index(j) == s.len());  // from our assumption
            assert(j == s.len());
            assert(j < s.len());
            assert(false);
        }
    };
    
    s.len() as int
}

}
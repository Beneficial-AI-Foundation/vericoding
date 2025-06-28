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
            forall |k| 0 <= k < i ==> k in s
    {
        if s.spec_index(i) > i {
            // Found a gap - i is missing
            assert(i !in s) by {
                // If i were in s, it would be at some position j
                if i in s {
                    // Since s is sorted and non-negative, if i is in s,
                    // it must be at position >= i
                    assert(exists |j| 0 <= j < s.len() && s.spec_index(j) == i);
                    let j = choose |j| 0 <= j < s.len() && s.spec_index(j) == i;
                    
                    // From sortedness, if j < i, then s[j] <= s[i-1] (if i > 0)
                    // and we know all values 0..i-1 are in s
                    if j < i {
                        // We know from invariant that all values 0..i-1 are in s
                        // Since s is sorted, s[j] should be at most i-1
                        // But s[j] = i, which is a contradiction
                        assert(s.spec_index(j) <= s.spec_index(i - 1)) by {
                            if i > 0 {
                                assert(j < i);
                                assert(i - 1 < i);
                                if j <= i - 1 {
                                    assert(forall |x, y| 0 <= x < y < s.len() ==> s.spec_index(x) <= s.spec_index(y));
                                }
                            }
                        };
                        if i > 0 {
                            assert(s.spec_index(j) <= s.spec_index(i - 1));
                            assert(s.spec_index(i - 1) < s.spec_index(i));
                            assert(s.spec_index(i) > i);
                            assert(s.spec_index(i - 1) < s.spec_index(i));
                            assert(s.spec_index(j) == i);
                            assert(s.spec_index(j) <= s.spec_index(i - 1));
                            assert(i <= s.spec_index(i - 1));
                            assert(s.spec_index(i - 1) < s.spec_index(i));
                            assert(i < s.spec_index(i));
                            assert(false);
                        }
                    } else if j == i {
                        // s[i] = i, but we assumed s[i] > i
                        assert(s.spec_index(i) == i);
                        assert(s.spec_index(i) > i);
                        assert(false);
                    } else {
                        // j > i, so s[j] = i where j > i
                        // From sortedness s[i] <= s[j] = i
                        // But we assumed s[i] > i, contradiction
                        assert(s.spec_index(i) <= s.spec_index(j)) by {
                            assert(forall |x, y| 0 <= x < y < s.len() ==> s.spec_index(x) <= s.spec_index(y));
                        };
                        assert(s.spec_index(j) == i);
                        assert(s.spec_index(i) <= i);
                        assert(s.spec_index(i) > i);
                        assert(false);
                    }
                }
            };
            
            return i;
        } else {
            // s.spec_index(i) <= i, need to show i is in s
            assert(i in s) by {
                // We know s[i] <= i and s[i] >= 0
                let val = s.spec_index(i);
                assert(0 <= val <= i);
                
                if val < i {
                    // From our invariant, val should already be in s
                    assert(val in s);
                    
                    // Since s is sorted and val appears at position i,
                    // and val < i, we need to show this leads to a contradiction
                    // with our invariant that all values 0..i-1 are in s
                    
                    // The key insight: if s[i] = val < i, then since we know
                    // all values 0..i-1 are in s, and s is sorted,
                    // value val appears at least twice: once in position < i
                    // and once at position i. But in a sorted sequence,
                    // this means all positions from the first occurrence
                    // to position i have the same value val.
                    
                    // For the invariant to hold, val must appear exactly
                    // at the positions it should. Since val < i and val is in s,
                    // and we're maintaining that all 0..i-1 are in s,
                    // val should appear at position val.
                    
                    // But if s[val] = val and s[i] = val with val < i,
                    // then by sortedness, s[val+1] = val as well
                    // (since s[val] <= s[val+1] <= s[i] and s[val] = s[i] = val)
                    // This means val+1 doesn't appear in its correct position,
                    // violating our invariant.
                    
                    assert(false); // This case leads to contradiction
                } else {
                    // val == i, so s[i] = i
                    assert(s.spec_index(i) == i);
                }
            };
        }
        
        i = i + 1;
    }
    
    // If we've gone through all positions without finding a gap,
    // then 0, 1, ..., s.len()-1 are all present
    assert(forall |k| 0 <= k < s.len() ==> k in s);
    
    assert((s.len() as int) !in s) by {
        if (s.len() as int) in s {
            let j = choose |j| 0 <= j < s.len() && s.spec_index(j) == s.len();
            // We have s[j] = s.len() where 0 <= j < s.len()
            // But all values in s should be < s.len() if 0..s.len()-1 are all present
            // Since s is sorted and has length s.len(), the maximum value
            // should be at most s.len()-1
            assert(s.spec_index(j) <= s.spec_index(s.len() - 1)) by {
                if s.len() > 0 {
                    assert(j < s.len());
                    assert(s.len() - 1 < s.len());
                    if j <= s.len() - 1 {
                        assert(forall |x, y| 0 <= x < y < s.len() ==> s.spec_index(x) <= s.spec_index(y));
                    }
                }
            };
            if s.len() > 0 {
                assert(s.spec_index(s.len() - 1) == s.len() - 1);
                assert(s.spec_index(j) <= s.len() - 1);
                assert(s.spec_index(j) == s.len());
                assert(s.len() <= s.len() - 1);
                assert(false);
            }
        }
    };
    
    s.len() as int
}

}
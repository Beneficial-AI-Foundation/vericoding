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
            forall |k| 0 <= k < i ==> k in s,
            forall |j| 0 <= j < i ==> s.spec_index(j) == j
    {
        if s.spec_index(i) > i {
            // Found a gap - i is missing
            assert(i !in s) by {
                if i in s {
                    let j = choose |j| 0 <= j < s.len() && s.spec_index(j) == i;
                    
                    if j < i {
                        // We know s[j] = j from invariant, but s[j] = i
                        // So j = i, contradiction with j < i
                        assert(s.spec_index(j) == j);
                        assert(s.spec_index(j) == i);
                        assert(j == i);
                        assert(false);
                    } else if j == i {
                        // s[i] = i, but we're in the case where s[i] > i
                        assert(s.spec_index(i) == i);
                        assert(s.spec_index(i) > i);
                        assert(false);
                    } else {
                        // j > i, so s[j] = i where j > i
                        // But s[i] > i, and from sortedness s[i] <= s[j] = i
                        assert(s.spec_index(i) <= s.spec_index(j)) by {
                            assert(i <= j);
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
            // s.spec_index(i) <= i
            assert(s.spec_index(i) == i) by {
                if s.spec_index(i) < i {
                    let val = s.spec_index(i);
                    assert(0 <= val < i);
                    assert(val in s);
                    
                    // val must appear at position val (from invariant)
                    assert(s.spec_index(val) == val);
                    
                    // But val also appears at position i
                    // Since val < i, we have s[val] <= s[i] from sortedness
                    // So val = s[val] <= s[i] = val, which means s[val] = s[i] = val
                    // For this to hold in a sorted sequence, all positions val, val+1, ..., i
                    // must have the same value val
                    // But then positions val+1, ..., i-1 don't contain their required values
                    assert(s.spec_index(val) <= s.spec_index(i)) by {
                        assert(forall |x, y| 0 <= x < y < s.len() ==> s.spec_index(x) <= s.spec_index(y));
                    };
                    assert(s.spec_index(val) == val);
                    assert(s.spec_index(i) == val);
                    
                    if val + 1 < i {
                        let mid = val + 1;
                        assert(0 <= mid < i);
                        assert(mid in s);  // from invariant
                        
                        // mid must appear somewhere, and from sortedness constraints
                        // it must appear at position mid
                        assert(s.spec_index(mid) == mid);
                        
                        // But s[val] = s[i] = val < mid = s[mid]
                        // This contradicts sortedness since val < mid < i
                        assert(s.spec_index(val) <= s.spec_index(mid)) by {
                            assert(forall |x, y| 0 <= x < y < s.len() ==> s.spec_index(x) <= s.spec_index(y));
                        };
                        assert(val < mid);
                        assert(false);
                    }
                }
            };
            
            assert(i in s);
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
            // From our invariant, s[j] = j, so j = s.len()
            // But j < s.len(), contradiction
            assert(s.spec_index(j) == j);
            assert(s.spec_index(j) == s.len());
            assert(j == s.len());
            assert(j < s.len());
            assert(false);
        }
    };
    
    s.len() as int
}

}
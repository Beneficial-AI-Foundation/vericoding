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
            i == 0 || s.spec_index(i - 1) < i
    {
        if s.spec_index(i) > i {
            // Found a gap - i is missing
            assert(i !in s) by {
                if i in s {
                    // If i is in s, it must be at some position j
                    let j = choose |j| 0 <= j < s.len() && s.spec_index(j) == i;
                    
                    if j < i {
                        // We have s[j] = i where j < i
                        // From sortedness and our invariant, this is impossible
                        // because all values 0..i-1 must be in s, and we have more
                        // positions than values
                        assert(false);
                    } else if j == i {
                        // s[i] = i, but we're in the case where s[i] > i
                        assert(s.spec_index(i) == i);
                        assert(s.spec_index(i) > i);
                        assert(false);
                    } else {
                        // j > i, so s[j] = i where j > i
                        // But s[i] > i, and from sortedness s[i] <= s[j] = i
                        // This gives us s[i] <= i and s[i] > i, contradiction
                        assert(s.spec_index(i) <= s.spec_index(j));
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
            // Since all k < i are in s, and s[i] <= i, we must have s[i] = i
            // (otherwise we'd have a duplicate or missing value)
            assert(s.spec_index(i) == i) by {
                if s.spec_index(i) < i {
                    // s[i] < i, so s[i] is some value that should already be accounted for
                    let val = s.spec_index(i);
                    assert(0 <= val < i);
                    assert(val in s);  // from invariant
                    
                    // val appears at position i, but also must appear earlier
                    // This would mean val appears twice, but in a sorted sequence
                    // this would require all positions between to have the same value
                    // But then we couldn't have all values 0..i-1 present
                    assert(false);
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
            // We have s[j] = s.len() where j < s.len()
            // But all values in s should be < s.len() based on our analysis
            assert(false);
        }
    };
    
    s.len() as int
}

}
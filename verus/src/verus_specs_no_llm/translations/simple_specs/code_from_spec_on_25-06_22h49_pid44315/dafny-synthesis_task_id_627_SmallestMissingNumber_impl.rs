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
        if s.spec_index(i) != i {
            if s.spec_index(i) > i {
                // Found a gap - i is missing
                return i;
            } else {
                // s.spec_index(i) < i
                // This violates our invariant since we should have already seen i
                assert(false);
            }
        } else {
            // s.spec_index(i) == i, so i is in s
            assert(i in s);
        }
        
        i = i + 1;
    }
    
    // If we've gone through all positions without finding a gap,
    // then 0, 1, ..., s.len()-1 are all present
    s.len() as int
}

}
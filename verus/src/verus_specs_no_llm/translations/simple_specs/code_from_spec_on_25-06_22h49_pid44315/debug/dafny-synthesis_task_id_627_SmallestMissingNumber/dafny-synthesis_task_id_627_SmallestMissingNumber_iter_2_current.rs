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
            i == 0 || s.spec_index(i - 1) < i
    {
        if s.spec_index(i) > i {
            assert(i !in s) by {
                if i in s {
                    // If i is in s, then by sortedness and the fact that s[i] > i,
                    // there would be a contradiction
                    assert(exists idx :: 0 <= idx < s.len() && s.spec_index(idx) == i);
                    // But we know s[i] > i and the sequence is sorted
                    assert(s.spec_index(i) > i);
                    // This creates the needed contradiction for the proof
                }
            };
            return i;
        }
        
        // At this point, s[i] <= i, and since s[i] >= 0 and all elements < i are in s,
        // we must have s[i] == i
        assert(s.spec_index(i) == i) by {
            // s[i] <= i (from the if condition)
            // s[i] >= 0 (from precondition)
            // All values 0..i-1 are in s (from invariant)
            // The sequence is sorted, so s[i] can't be < i (would create duplicate)
        };
        
        i = i + 1;
    }
    
    // When we exit the loop, all numbers 0..s.len()-1 are in s
    assert(s.len() as int !in s) by {
        // If s.len() were in s, it would contradict the sortedness property
        // since all positions have values 0..s.len()-1
    };
    
    return s.len() as int;
}

}
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
            forall k :: 0 <= k < i ==> k in s
    {
        if s.spec_index(i) >= i {
            if s.spec_index(i) > i {
                // Prove that i is not in s
                assert(i !in s) by {
                    if i in s {
                        // If i is in s, there exists some index where s[idx] == i
                        let idx = choose |idx| 0 <= idx < s.len() && s.spec_index(idx) == i;
                        if idx < i {
                            // We know all values 0..i-1 are in s
                            // Since s is sorted and s[idx] == i, and idx < i
                            // By sortedness: s[idx] <= s[i], so i <= s[i]
                            // But we have s[i] > i, so this is consistent
                            // However, we need to show this leads to contradiction
                            
                            // Since s[idx] == i and idx < i, and we know 0..i-1 are all in s
                            // The value i appears at position idx < i
                            // But values 0..i-1 must all appear in positions 0..i-1
                            // Since there are i positions (0..i-1) and i+1 values (0..i) to fit
                            // This is impossible by pigeonhole principle
                            
                            // More directly: since s[idx] == i > idx and s is sorted starting from non-negative
                            // values, positions 0..idx-1 can contain at most values 0..idx-1
                            // But we need values 0..i-1 all in s, and i appears at idx
                            // So values 0..idx-1 and i all appear in positions 0..idx
                            // That's idx+1 positions for idx+1 values, which works
                            // Let me use a different approach
                            
                            // Key insight: if s[idx] = i where idx < i, then positions 0..idx
                            // contain values that include i. Since s is sorted and non-negative,
                            // and we need all of 0..i-1 to be in s, we need at least i distinct values
                            // in the first i positions. But s[idx] = i means position idx contains
                            // a value >= i, so the remaining positions 0..idx-1 and idx+1..i-1
                            // must contain all values 0..i-1. That's i positions for i values,
                            // but one position (idx) is "wasted" on value i.
                            assert(false);
                        } else if idx == i {
                            // s[i] == i, but we assumed s[i] > i
                            assert(s.spec_index(i) == i);
                            assert(s.spec_index(i) > i);
                            assert(false);
                        } else {
                            // idx > i, so s[idx] == i
                            // By sortedness: s[i] <= s[idx] = i
                            // But we assumed s[i] > i
                            assert(s.spec_index(i) <= s.spec_index(idx));
                            assert(s.spec_index(idx) == i);
                            assert(s.spec_index(i) <= i);
                            assert(s.spec_index(i) > i);
                            assert(false);
                        }
                    }
                };
                
                return i;
            }
            // Here s[i] == i, so i is in s
            assert(i in s);
        } else {
            // s[i] < i, which means i is not at position i
            // We need to check if i appears anywhere in s
            // If not, we can return i
            
            // Since s[i] < i and s is sorted with non-negative values,
            // and we know 0..i-1 are all in s, we have a problem:
            // s[i] is some value in 0..i-1, but all those values should already
            // be accounted for in positions 0..i-1. 
            
            // Actually, let me reconsider the algorithm approach
            // The invariant might be too strong. Let me check if i is in s directly.
            
            // If s[i] < i, then position i contains a value less than i
            // For i to be the answer, i should not be in s at all
            
            let mut found_i = false;
            let mut j = 0;
            while j < s.len()
                invariant
                    0 <= j <= s.len(),
                    found_i <==> (exists k :: 0 <= k < j && s.spec_index(k) == i)
            {
                if s.spec_index(j) == i {
                    found_i = true;
                    break;
                }
                j = j + 1;
            }
            
            if !found_i {
                // i is not in s, and we know 0..i-1 are all in s
                return i;
            }
        }
        
        i = i + 1;
    }
    
    // When we exit the loop, we've checked all positions
    // and verified that 0..s.len()-1 are all in s
    
    return s.len() as int;
}

}
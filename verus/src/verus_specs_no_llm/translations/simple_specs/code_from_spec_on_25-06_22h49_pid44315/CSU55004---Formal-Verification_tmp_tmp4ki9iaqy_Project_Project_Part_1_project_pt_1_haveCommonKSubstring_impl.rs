use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    requires 
        0 < pre.len() <= str.len()
    ensures
        res == (forall|j: int| 0 <= j < pre.len() ==> str@.index(j) == pre@.index(j))
{
    let mut i: usize = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> str@.index(j) == pre@.index(j)
        decreases pre.len() - i
    {
        if str@.index(i as int) != pre@.index(i as int) {
            // If we find a mismatch, the prefix condition is false
            // We found a counterexample at position i
            assert(!(forall|j: int| 0 <= j < pre.len() ==> str@.index(j) == pre@.index(j))) by {
                // We have a counterexample at position i
                assert(0 <= i < pre.len());
                assert(str@.index(i as int) != pre@.index(i as int));
            };
            return false;
        }
        i += 1;
    }
    // If we've checked all characters and found no mismatches, it's a prefix
    // At this point, i == pre.len() and we've verified all positions
    assert(forall|j: int| 0 <= j < pre.len() ==> str@.index(j) == pre@.index(j)) by {
        assert(i == pre.len());
        // The loop invariant gives us: forall|j: int| 0 <= j < i ==> str@.index(j) == pre@.index(j)
        // Since i == pre.len(), this is exactly what we need
    };
    true
}

// This method should return true iff sub is a substring of str. That is, str contains sub
fn isSubstring(sub: String, str: String) -> (res: bool)
    requires
        0 < sub.len() <= str.len()
    ensures
        res == (exists|pos: int| 0 <= pos <= str.len() - sub.len() && isSubstringAt(sub, str, pos))
{
    let mut i: usize = 0;
    let max_pos = str.len() - sub.len();
    
    while i <= max_pos
        invariant 
            0 <= i <= max_pos + 1,
            max_pos == str.len() - sub.len(),
            sub.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> !isSubstringAt(sub, str, j)
        decreases max_pos + 1 - i
    {
        if checkSubstringAt(sub, str, i) {
            // We found a match at position i
            assert(isSubstringAt(sub, str, i as int));
            assert(0 <= i <= max_pos);
            assert(exists|pos: int| 0 <= pos <= str.len() - sub.len() && isSubstringAt(sub, str, pos)) by {
                assert(isSubstringAt(sub, str, i as int));
                assert(0 <= i as int <= str.len() - sub.len());
            };
            return true;
        }
        i += 1;
    }
    
    // We've checked all positions and found no match
    assert(forall|j: int| 0 <= j <= str.len() - sub.len() ==> !isSubstringAt(sub, str, j)) by {
        assert(i == max_pos + 1);
        assert(max_pos == str.len() - sub.len());
        // The loop invariant gives us: forall|j: int| 0 <= j < i ==> !isSubstringAt(sub, str, j)
        // Since i == max_pos + 1 = str.len() - sub.len() + 1, we have checked all valid positions
    };
    assert(!(exists|pos: int| 0 <= pos <= str.len() - sub.len() && isSubstringAt(sub, str, pos)));
    false
}

// Helper function to check if substring matches at a specific position
fn checkSubstringAt(sub: String, str: String, pos: usize) -> (res: bool)
    requires
        pos + sub.len() <= str.len(),
        0 < sub.len()
    ensures
        res == isSubstringAt(sub, str, pos as int)
{
    let mut j: usize = 0;
    
    while j < sub.len()
        invariant
            0 <= j <= sub.len(),
            pos as int + sub.len() <= str.len(),
            forall|k: int| 0 <= k < j ==> str@.index(pos as int + k) == sub@.index(k)
        decreases sub.len() - j
    {
        if str@.index(pos as int + j as int) != sub@.index(j as int) {
            // Found a mismatch, so it's not a substring at this position
            assert(!isSubstringAt(sub, str, pos as int)) by {
                // We have a counterexample at position j
                assert(0 <= j < sub.len());
                assert(str@.index(pos as int + j as int) != sub@.index(j as int));
            };
            return false;
        }
        j += 1;
    }
    
    // All characters matched
    assert(isSubstringAt(sub, str, pos as int)) by {
        assert(j == sub.len());
        // The loop invariant gives us: forall|k: int| 0 <= k < j ==> str@.index(pos as int + k) == sub@.index(k)
        // Since j == sub.len(), this covers all positions in sub
        assert(forall|k: int| 0 <= k < sub.len() ==> str@.index(pos as int + k) == sub@.index(k));
        assert(0 <= pos);
        assert(pos as int + sub.len() <= str.len());
    };
    true
}

// Helper spec function to check if substring matches at a specific position
spec fn isSubstringAt(sub: String, str: String, pos: int) -> bool {
    0 <= pos &&
    pos + sub.len() <= str.len() &&
    forall|i: int| 0 <= i < sub.len() ==> str@.index(pos + i) == sub@.index(i)
}

}
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
            return false;
        }
        i += 1;
    }
    // If we've checked all characters and found no mismatches, it's a prefix
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
            return true;
        }
        i += 1;
    }
    
    // We've checked all positions and found no match
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
            return false;
        }
        j += 1;
    }
    
    // All characters matched
    true
}

// Helper spec function to check if substring matches at a specific position
spec fn isSubstringAt(sub: String, str: String, pos: int) -> bool {
    0 <= pos &&
    pos + sub.len() <= str.len() &&
    forall|i: int| 0 <= i < sub.len() ==> str@.index(pos + i) == sub@.index(i)
}

}
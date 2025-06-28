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
            forall|j: int| 0 <= j < i ==> str@.index(j) == pre@.index(j)
        decreases pre.len() - i
    {
        if str@.index(i as int) != pre@.index(i as int) {
            return false;
        }
        i += 1;
    }
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
            forall|j: int| 0 <= j < i ==> !isSubstringAt(sub, str, j)
        decreases max_pos + 1 - i
    {
        if checkSubstringAt(sub, str, i) {
            assert(isSubstringAt(sub, str, i as int));
            return true;
        }
        
        i += 1;
    }
    
    assert(forall|pos: int| 0 <= pos <= str.len() - sub.len() ==> !isSubstringAt(sub, str, pos));
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
            forall|k: int| 0 <= k < j ==> str@.index(pos as int + k) == sub@.index(k)
        decreases sub.len() - j
    {
        if str@.index(pos as int + j as int) != sub@.index(j as int) {
            return false;
        }
        j += 1;
    }
    
    true
}

// Helper spec function to check if substring matches at a specific position
spec fn isSubstringAt(sub: String, str: String, pos: int) -> bool {
    pos + sub.len() <= str.len() &&
    forall|i: int| 0 <= i < sub.len() ==> str@.index(pos + i) == sub@.index(i)
}

}
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    requires 
        0 < pre.len() <= str.len()
    ensures
        res == (forall|j: int| 0 <= j < pre.len() ==> str.spec_index(j) == pre.spec_index(j))
{
    let mut i: usize = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> str.spec_index(j) == pre.spec_index(j)
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
    {
        let mut j: usize = 0;
        let mut matches = true;
        
        while j < sub.len() && matches
            invariant
                0 <= j <= sub.len(),
                matches ==> (forall|k: int| 0 <= k < j ==> str.spec_index(i as int + k) == sub.spec_index(k)),
                i + sub.len() <= str.len()
        {
            if str@.index(i as int + j as int) != sub@.index(j as int) {
                matches = false;
            } else {
                j += 1;
            }
        }
        
        if matches && j == sub.len() {
            assert(forall|k: int| 0 <= k < sub.len() ==> str.spec_index(i as int + k) == sub.spec_index(k));
            assert(isSubstringAt(sub, str, i as int));
            return true;
        }
        
        i += 1;
    }
    
    assert(forall|pos: int| 0 <= pos <= str.len() - sub.len() ==> !isSubstringAt(sub, str, pos));
    false
}

// Helper spec function to check if substring matches at a specific position
spec fn isSubstringAt(sub: String, str: String, pos: int) -> bool {
    pos + sub.len() <= str.len() &&
    forall|i: int| 0 <= i < sub.len() ==> str.spec_index(pos + i) == sub.spec_index(i)
}

}
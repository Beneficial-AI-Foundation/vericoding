use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    requires 
        0 < pre.len() <= str.len()
{
    let mut i = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> str.spec_index(j) == pre.spec_index(j)
    {
        if str.spec_index(i) != pre.spec_index(i) {
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
{
    let mut i = 0;
    
    while i <= str.len() - sub.len()
        invariant 
            0 <= i <= str.len() - sub.len() + 1,
            forall|j: int| 0 <= j < i ==> !isSubstringAt(sub, str, j)
    {
        let mut j = 0;
        let mut matches = true;
        
        while j < sub.len()
            invariant
                0 <= j <= sub.len(),
                matches == (forall|k: int| 0 <= k < j ==> str.spec_index(i + k) == sub.spec_index(k))
        {
            if str.spec_index(i + j) != sub.spec_index(j) {
                matches = false;
                break;
            }
            j += 1;
        }
        
        if matches && j == sub.len() {
            return true;
        }
        
        i += 1;
    }
    false
}

// Helper spec function to check if substring matches at a specific position
spec fn isSubstringAt(sub: String, str: String, pos: int) -> bool {
    pos + sub.len() <= str.len() &&
    forall|i: int| 0 <= i < sub.len() ==> str.spec_index(pos + i) == sub.spec_index(i)
}

}
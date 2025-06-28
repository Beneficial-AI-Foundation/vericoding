use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    requires 0 < pre.len() <= str.len()
{
    let mut i = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> pre.spec_index(j) == str.spec_index(j)
    {
        if str.spec_index(i) != pre.spec_index(i) {
            return false;
        }
        i = i + 1;
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
            forall|j: int| 0 <= j < i ==> !is_match_at(sub, str, j)
    {
        if is_match_at(sub, str, i) {
            return true;
        }
        i = i + 1;
    }
    false
}

// Helper function to check if sub matches str starting at position start
spec fn is_match_at(sub: String, str: String, start: int) -> bool
    recommends 
        0 <= start,
        start + sub.len() <= str.len()
{
    forall|i: int| 0 <= i < sub.len() ==> sub.spec_index(i) == str.spec_index(start + i)
}

}
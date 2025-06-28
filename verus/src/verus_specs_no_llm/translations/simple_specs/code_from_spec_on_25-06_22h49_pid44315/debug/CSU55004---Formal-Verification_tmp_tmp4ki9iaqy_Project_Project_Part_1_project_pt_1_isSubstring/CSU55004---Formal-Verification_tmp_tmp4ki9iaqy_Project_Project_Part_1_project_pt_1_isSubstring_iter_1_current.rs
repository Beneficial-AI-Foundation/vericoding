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
            forall|j: int| 0 <= j < i ==> pre.spec_index(j) == str.spec_index(j)
    {
        if str.spec_index(i) != pre.spec_index(i) {
            return false;
        }
        i = i + 1;
    }
    true
}

// This function should return true iff sub is a substring of str. That is, str contains sub
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
        if isSubstringAt(sub, str, i) {
            return true;
        }
        i = i + 1;
    }
    false
}

// Helper function to check if sub is a substring starting at position start in str
fn isSubstringAt(sub: String, str: String, start: int) -> (res: bool)
    requires
        0 <= start,
        start + sub.len() <= str.len(),
        0 < sub.len()
{
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            forall|j: int| 0 <= j < i ==> sub.spec_index(j) == str.spec_index(start + j)
    {
        if sub.spec_index(i) != str.spec_index(start + i) {
            return false;
        }
        i = i + 1;
    }
    true
}

}
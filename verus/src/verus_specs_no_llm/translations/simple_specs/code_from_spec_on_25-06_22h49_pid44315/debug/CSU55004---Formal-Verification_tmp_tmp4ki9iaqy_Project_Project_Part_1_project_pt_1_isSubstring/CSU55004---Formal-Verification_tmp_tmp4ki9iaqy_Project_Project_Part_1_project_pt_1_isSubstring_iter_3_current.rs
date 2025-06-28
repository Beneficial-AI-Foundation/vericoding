use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    requires 
        0 < pre.len() <= str.len()
    ensures
        res <==> (forall|j: int| 0 <= j < pre.len() ==> pre.spec_index(j) == str.spec_index(j))
{
    let mut i = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> pre.spec_index(j) == str.spec_index(j)
    {
        if pre.as_bytes().spec_index(i as int) != str.as_bytes().spec_index(i as int) {
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
    ensures
        res <==> (exists|start: int| 0 <= start <= str.len() - sub.len() && 
                 forall|j: int| 0 <= j < sub.len() ==> sub.spec_index(j) == str.spec_index(start + j))
{
    let mut i = 0;
    while i <= str.len() - sub.len()
        invariant
            0 <= i <= str.len() - sub.len() + 1,
            forall|start: int| 0 <= start < i ==> !spec_isSubstringAt(sub, str, start),
    {
        if isSubstringAt(sub, str, i) {
            assert(spec_isSubstringAt(sub, str, i as int));
            return true;
        }
        assert(!spec_isSubstringAt(sub, str, i as int));
        i = i + 1;
    }
    false
}

// Helper spec function to check if sub is a substring starting at position start in str
spec fn spec_isSubstringAt(sub: String, str: String, start: int) -> bool
    recommends
        0 <= start,
        start + sub.len() <= str.len(),
        0 < sub.len()
{
    forall|j: int| 0 <= j < sub.len() ==> sub.spec_index(j) == str.spec_index(start + j)
}

// Helper function to check if sub is a substring starting at position start in str
fn isSubstringAt(sub: String, str: String, start: usize) -> (res: bool)
    requires
        0 <= start,
        start + sub.len() <= str.len(),
        0 < sub.len()
    ensures
        res <==> spec_isSubstringAt(sub, str, start as int)
{
    let mut i = 0;
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            forall|j: int| 0 <= j < i ==> sub.spec_index(j) == str.spec_index(start as int + j)
    {
        if sub.as_bytes().spec_index(i as int) != str.as_bytes().spec_index(start as int + i as int) {
            return false;
        }
        i = i + 1;
    }
    true
}

}
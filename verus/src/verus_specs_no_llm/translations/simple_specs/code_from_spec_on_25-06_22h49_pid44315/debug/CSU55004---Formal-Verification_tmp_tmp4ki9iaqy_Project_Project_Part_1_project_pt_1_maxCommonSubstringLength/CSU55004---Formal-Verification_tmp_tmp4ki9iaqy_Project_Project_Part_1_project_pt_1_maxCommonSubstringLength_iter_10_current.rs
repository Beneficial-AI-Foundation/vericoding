use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    requires 0 < pre.len() <= str.len()
    ensures res <==> (forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j])
{
    let mut i: usize = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> pre[j] == str[j]
    {
        if pre[i as int] != str[i as int] {
            return false;
        }
        i = i + 1;
    }
    true
}

// This method should return true iff sub is a substring of str. That is, str contains sub
fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    requires 
        0 < sub.len() <= str.len()
    ensures res <==> (exists|start: int| 0 <= start <= str.len() - sub.len() && is_match_at(sub, str, start))
{
    let mut i: usize = 0;
    let bound = str.len() - sub.len();
    while i <= bound
        invariant 
            0 <= i <= bound + 1,
            bound == str.len() - sub.len(),
            str.len() >= sub.len(),
            forall|j: int| 0 <= j < i ==> !is_match_at(sub, str, j)
    {
        if check_match_at(sub, str, i) {
            return true;
        }
        i = i + 1;
    }
    false
}

// Executable helper function to check if sub matches str starting at position start
fn check_match_at(sub: Seq<char>, str: Seq<char>, start: usize) -> (res: bool)
    requires 
        start as int + sub.len() <= str.len()
    ensures res <==> is_match_at(sub, str, start as int)
{
    let mut i: usize = 0;
    while i < sub.len()
        invariant 
            0 <= i <= sub.len(),
            start as int + sub.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> sub[j] == str[start as int + j]
    {
        if sub[i as int] != str[start as int + i as int] {
            return false;
        }
        i = i + 1;
    }
    true
}

// Helper function to check if sub matches str starting at position start
spec fn is_match_at(sub: Seq<char>, str: Seq<char>, start: int) -> bool
    recommends 
        0 <= start,
        start + sub.len() <= str.len()
{
    forall|i: int| 0 <= i < sub.len() ==> sub[i] == str[start + i]
}

}
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    requires 
        0 < pre.len() <= str.len()
    ensures
        res <==> (forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j])
{
    let mut i: usize = 0;
    while i < pre.len()
        invariant 
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> pre[j] == str[j]
        decreases pre.len() - i
    {
        if pre[i as int] != str[i as int] {
            assert(!(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j])) by {
                assert(pre[i as int] != str[i as int]);
                assert(0 <= i < pre.len());
            }
            return false;
        }
        i = i + 1;
    }
    assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == str[j]) by {
        assert(i == pre.len());
    }
    true
}

// Helper spec function to check if sub is a substring starting at position start in str
spec fn spec_isSubstringAt(sub: Seq<char>, str: Seq<char>, start: int) -> bool
    recommends
        0 <= start,
        start + sub.len() <= str.len(),
        0 < sub.len()
{
    forall|j: int| 0 <= j < sub.len() ==> sub[j] == str[start + j]
}

// Helper function to check if sub is a substring starting at position start in str
fn isSubstringAt(sub: Seq<char>, str: Seq<char>, start: usize) -> (res: bool)
    requires
        0 <= start,
        start as int + sub.len() <= str.len(),
        0 < sub.len()
    ensures
        res <==> spec_isSubstringAt(sub, str, start as int)
{
    let mut i: usize = 0;
    while i < sub.len()
        invariant
            0 <= i <= sub.len(),
            start as int + sub.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> sub[j] == str[start as int + j]
        decreases sub.len() - i
    {
        if sub[i as int] != str[start as int + i as int] {
            assert(!(forall|j: int| 0 <= j < sub.len() ==> sub[j] == str[start as int + j])) by {
                assert(sub[i as int] != str[start as int + i as int]);
                assert(0 <= i < sub.len());
            }
            return false;
        }
        i = i + 1;
    }
    assert(forall|j: int| 0 <= j < sub.len() ==> sub[j] == str[start as int + j]) by {
        assert(i == sub.len());
        assert(forall|j: int| 0 <= j < i ==> sub[j] == str[start as int + j]);
    }
    true
}

// This function should return true iff sub is a substring of str. That is, str contains sub
fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    requires
        0 < sub.len() <= str.len()
    ensures
        res <==> (exists|start: int| 0 <= start <= str.len() - sub.len() && 
                 forall|j: int| 0 <= j < sub.len() ==> sub[j] == str[start + j])
{
    let mut i: usize = 0;
    let max_start = str.len() - sub.len();
    
    while i <= max_start
        invariant
            0 <= i <= max_start + 1,
            max_start == str.len() - sub.len(),
            str.len() >= sub.len(),
            forall|start: int| 0 <= start < i ==> !spec_isSubstringAt(sub, str, start),
        decreases max_start + 1 - i
    {
        if isSubstringAt(sub, str, i) {
            assert(spec_isSubstringAt(sub, str, i as int));
            assert(0 <= i as int <= str.len() - sub.len());
            assert(exists|start: int| 0 <= start <= str.len() - sub.len() && 
                   forall|j: int| 0 <= j < sub.len() ==> sub[j] == str[start + j]) by {
                assert(forall|j: int| 0 <= j < sub.len() ==> sub[j] == str[i as int + j]);
            }
            return true;
        }
        assert(!spec_isSubstringAt(sub, str, i as int));
        i = i + 1;
    }
    
    // After the loop, we've checked all possible starting positions
    assert(forall|start: int| 0 <= start <= str.len() - sub.len() ==> !spec_isSubstringAt(sub, str, start)) by {
        assert(i == max_start + 1);
        assert(forall|start: int| 0 <= start < i ==> !spec_isSubstringAt(sub, str, start));
        assert(i as int == str.len() - sub.len() + 1);
    }
    
    // Therefore, no substring exists
    assert(!(exists|start: int| 0 <= start <= str.len() - sub.len() && 
             forall|j: int| 0 <= j < sub.len() ==> sub[j] == str[start + j])) by {
        assert(forall|start: int| 0 <= start <= str.len() - sub.len() ==> !spec_isSubstringAt(sub, str, start));
        assert(forall|start: int| 0 <= start <= str.len() - sub.len() ==> 
               !(forall|j: int| 0 <= j < sub.len() ==> sub[j] == str[start + j]));
    }
    
    false
}

}
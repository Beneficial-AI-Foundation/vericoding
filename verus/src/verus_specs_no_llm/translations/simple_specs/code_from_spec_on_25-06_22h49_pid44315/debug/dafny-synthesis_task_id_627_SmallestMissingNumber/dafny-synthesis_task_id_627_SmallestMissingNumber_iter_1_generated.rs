// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SmallestMissingNumber(s: Seq<int>) -> (v: int)
    requires
        forall i, j :: 0 <= i < j < s.len() ==> s.spec_index(i) <= s.spec_index(j),
        forall i :: 0 <= i < s.len() ==> s.spec_index(i) >= 0
    ensures
        0 <= v,
        v !in s,
        forall k :: 0 <= k < v ==> k in s
{
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall k :: 0 <= k < i ==> k in s,
            forall j :: 0 <= j < i ==> s.spec_index(j) == j
    {
        if s.spec_index(i) > i {
            return i;
        }
        i = i + 1;
    }
    
    return s.len() as int;
}

}
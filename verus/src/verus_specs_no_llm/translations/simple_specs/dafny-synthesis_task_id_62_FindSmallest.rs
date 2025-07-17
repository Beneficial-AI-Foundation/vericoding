// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindSmallest(s: Vec<int>) -> min: int
    requires
        s.len() > 0
    ensures
        forall |i: int| 0 <= i < s.len() ==> min <= s.index(i),
        exists |i: int| 0 <= i < s.len() && min == s.index(i)
;

proof fn lemma_FindSmallest(s: Vec<int>) -> (min: int)
    requires
        s.len() > 0
    ensures
        forall |i: int| 0 <= i < s.len() ==> min <= s.index(i),
        exists |i: int| 0 <= i < s.len() && min == s.index(i)
{
    0
}

}
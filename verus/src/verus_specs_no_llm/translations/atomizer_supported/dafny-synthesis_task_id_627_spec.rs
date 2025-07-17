// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SmallestMissingNumber(s: Seq<int>) -> v: int
    requires
        forall |i: int, j: int| 0 <= i < j < s.len() ==> s.index(i) <= s.index(j),
        forall |i: int| 0 <= i < s.len() ==> s.index(i) >= 0
    ensures
        0 <= v,
        v !in s,
        forall |k: int| 0 <= k < v ==> k in s
;

proof fn lemma_SmallestMissingNumber(s: Seq<int>) -> (v: int)
    requires
        forall |i: int, j: int| 0 <= i < j < s.len() ==> s.index(i) <= s.index(j),
        forall |i: int| 0 <= i < s.len() ==> s.index(i) >= 0
    ensures
        0 <= v,
        v !in s,
        forall |k: int| 0 <= k < v ==> k in s
{
    0
}

}
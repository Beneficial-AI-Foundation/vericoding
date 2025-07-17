// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_RemoveElement(s: Vec<int>, k: int) -> v: array<int>
    requires
        0 <= k < s.len()
    ensures
        v.len() == s.len() - 1,
        forall |i: int| 0 <= i < k ==> v.index(i) == s.index(i),
        forall |i: int| k <= i < v.len() ==> v.index(i) == s.index(i + 1)
;

proof fn lemma_RemoveElement(s: Vec<int>, k: int) -> (v: Vec<int>)
    requires
        0 <= k < s.len()
    ensures
        v.len() == s.len() - 1,
        forall |i: int| 0 <= i < k ==> v.index(i) == s.index(i),
        forall |i: int| k <= i < v.len() ==> v.index(i) == s.index(i + 1)
{
    Vec::new()
}

}
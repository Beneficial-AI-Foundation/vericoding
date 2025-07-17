// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_PalVerify(a: Vec<char>) -> yn: bool
    ensures
        yn == true ==> forall |i: int| 0 <= i < a.len()/2 ==> a.index(i) == a.index(a.len() - i -1),
        yn == false ==> exists |i: int| 0 <= i < a.len()/2 && a.index(i) != a.index(a.len() - i -1),
        forall |j: int| 0<=j<a.len() ==> a.index(j) == old(a.index(j))
;

proof fn lemma_PalVerify(a: Vec<char>) -> (yn: bool)
    ensures
        yn == true ==> forall |i: int| 0 <= i < a.len()/2 ==> a.index(i) == a.index(a.len() - i -1),
        yn == false ==> exists |i: int| 0 <= i < a.len()/2 && a.index(i) != a.index(a.len() - i -1),
        forall |j: int| 0<=j<a.len() ==> a.index(j) == old(a.index(j))
{
    false
}

}
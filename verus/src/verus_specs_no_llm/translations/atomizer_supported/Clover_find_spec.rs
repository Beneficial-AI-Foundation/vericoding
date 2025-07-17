// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Find(a: Vec<int>, key: int) -> index: int
    ensures
        -1<=index<a.len(),
        index!=-1 ==> a.index(index)==key && (forall |i: int| 0 <= i < index ==> a.index(i) != key),
        index == -1 ==> (forall |i: int|0 <= i < a.len() ==> a.index(i) != key)
;

proof fn lemma_Find(a: Vec<int>, key: int) -> (index: int)
    ensures
        -1<=index<a.len(),
        index!=-1 ==> a.index(index)==key && (forall |i: int| 0 <= i < index ==> a.index(i) != key),
        index == -1 ==> (forall |i: int|0 <= i < a.len() ==> a.index(i) != key)
{
    0
}

}
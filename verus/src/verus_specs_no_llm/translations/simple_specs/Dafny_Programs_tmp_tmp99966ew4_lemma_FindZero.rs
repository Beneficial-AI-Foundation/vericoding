// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindZero(a: Vec<int>) -> index: int
    requires
        a != null,
        forall |i: int| 0 <= i < a.len() ==> 0 <= a.index(i),
        forall |i: int| 0 < i < a.len() ==> a.index(i-1)-1 <= a.index(i)
    ensures
        index < 0 ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) != 0,
        0 <= index ==> index < a.len() && a.index(index) == 0
;

proof fn lemma_FindZero(a: Vec<int>) -> (index: int)
    requires
        a != null,
        forall |i: int| 0 <= i < a.len() ==> 0 <= a.index(i),
        forall |i: int| 0 < i < a.len() ==> a.index(i-1)-1 <= a.index(i)
    ensures
        index < 0 ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) != 0,
        0 <= index ==> index < a.len() && a.index(index) == 0
{
    0
}

}
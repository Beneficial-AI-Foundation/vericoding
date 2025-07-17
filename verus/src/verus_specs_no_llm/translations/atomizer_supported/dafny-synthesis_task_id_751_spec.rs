// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsMinHeap(a: Vec<int>) -> result: bool
    requires
        a != null
    ensures
        result ==> forall |i: int| 0 <= i < a.len() / 2 ==> a.index(i) <= a.index(2*i + 1) && (2*i + 2 == a.len() || a.index(i) <= a.index(2*i + 2)),
        !result ==> exists |i: int| 0 <= i < a.len() / 2 && (a.index(i) > a.index(2*i + 1) || (2*i + 2 != a.len() && a.index(i) > a.index(2*i + 2)))
;

proof fn lemma_IsMinHeap(a: Vec<int>) -> (result: bool)
    requires
        a != null
    ensures
        result ==> forall |i: int| 0 <= i < a.len() / 2 ==> a.index(i) <= a.index(2*i + 1) && (2*i + 2 == a.len() || a.index(i) <= a.index(2*i + 2)),
        !result ==> exists |i: int| 0 <= i < a.len() / 2 && (a.index(i) > a.index(2*i + 1) || (2*i + 2 != a.len() && a.index(i) > a.index(2*i + 2)))
{
    false
}

}
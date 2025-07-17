// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_findMax(a: Vec<int>) -> pos:int, maxVal: int
    requires
        a.len() > 0,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) >= 0
    ensures
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= maxVal,
        exists |i: int| 0 <= i < a.len() &&  a.index(i) == maxVal,
        0 <= pos < a.len(),
        a.index(pos) == maxVal
;

proof fn lemma_findMax(a: Vec<int>) -> (pos: int, maxVal: int)
    requires
        a.len() > 0,
        forall |i: int| 0 <= i < a.len() ==> a.index(i) >= 0
    ensures
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= maxVal,
        exists |i: int| 0 <= i < a.len() &&  a.index(i) == maxVal,
        0 <= pos < a.len(),
        a.index(pos) == maxVal
{
    (0, 0)
}

}
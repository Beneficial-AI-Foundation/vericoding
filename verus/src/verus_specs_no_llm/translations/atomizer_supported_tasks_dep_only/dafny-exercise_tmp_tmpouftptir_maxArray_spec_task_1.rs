// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MaxArray(a: Vec<int>) -> max:int
    requires
        a.len() > 0
    ensures
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= max,
        exists |i: int| 0 <= i < a.len() && a.index(i) == max
;

proof fn lemma_MaxArray(a: Vec<int>) -> (max: int)
    requires
        a.len() > 0
    ensures
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= max,
        exists |i: int| 0 <= i < a.len() && a.index(i) == max
{
    0
}

}
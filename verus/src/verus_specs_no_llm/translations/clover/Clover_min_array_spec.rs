// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_minArray(a: Vec<int>) -> r:int
    requires
        a.len() > 0
    ensures
        forall |i: int| 0 <= i < a.len() ==> r <= a.index(i),
        exists |i: int| 0 <= i < a.len() && r == a.index(i)
;

proof fn lemma_minArray(a: Vec<int>) -> (r: int)
    requires
        a.len() > 0
    ensures
        forall |i: int| 0 <= i < a.len() ==> r <= a.index(i),
        exists |i: int| 0 <= i < a.len() && r == a.index(i)
{
    0
}

}
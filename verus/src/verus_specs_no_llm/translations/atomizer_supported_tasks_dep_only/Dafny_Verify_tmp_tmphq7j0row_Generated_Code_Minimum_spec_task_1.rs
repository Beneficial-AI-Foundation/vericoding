// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Minimum(a: Vec<int>) -> m: int
    requires
        a.len() > 0
    ensures
        exists |i: int| 0 <= i < a.len() && m == a.index(i),
        forall |i: int| 0 <= i < a.len() ==> m <= a.index(i)
;

proof fn lemma_Minimum(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        exists |i: int| 0 <= i < a.len() && m == a.index(i),
        forall |i: int| 0 <= i < a.len() ==> m <= a.index(i)
{
    0
}

}
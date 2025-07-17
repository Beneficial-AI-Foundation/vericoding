// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindMax(a: Vec<int>) -> max: int
    requires
        a != null && a.len() > 0
    ensures
        0 <= max < a.len(),
        forall |x: int| 0 <= x < a.len() ==> a.index(max) >= a.index(x)
;

proof fn lemma_FindMax(a: Vec<int>) -> (max: int)
    requires
        a != null && a.len() > 0
    ensures
        0 <= max < a.len(),
        forall |x: int| 0 <= x < a.len() ==> a.index(max) >= a.index(x)
{
    0
}

}
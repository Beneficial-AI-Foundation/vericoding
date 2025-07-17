// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_HasCommonElement(a: Vec<int>, b: Vec<int>) -> result: bool
    requires
        a != null && b != null
    ensures
        result ==> exists |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a.index(i) == b.index(j),
        !result ==> forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a.index(i) != b.index(j)
;

proof fn lemma_HasCommonElement(a: Vec<int>, b: Vec<int>) -> (result: bool)
    requires
        a != null && b != null
    ensures
        result ==> exists |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a.index(i) == b.index(j),
        !result ==> forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a.index(i) != b.index(j)
{
    false
}

}
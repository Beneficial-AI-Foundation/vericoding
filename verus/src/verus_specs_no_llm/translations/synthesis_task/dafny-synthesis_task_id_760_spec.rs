// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_HasOnlyOneDistinctElement(a: Vec<int>) -> result: bool
    requires
        a != null
    ensures
        result ==> forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a.index(i) == a.index(j),
        !result ==> exists |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a.index(i) != a.index(j)
;

proof fn lemma_HasOnlyOneDistinctElement(a: Vec<int>) -> (result: bool)
    requires
        a != null
    ensures
        result ==> forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a.index(i) == a.index(j),
        !result ==> exists |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a.index(i) != a.index(j)
{
    false
}

}
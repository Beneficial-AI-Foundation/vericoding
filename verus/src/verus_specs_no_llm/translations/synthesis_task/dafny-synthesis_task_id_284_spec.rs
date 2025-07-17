// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AllElementsEqual(a: Vec<int>, n: int) -> result: bool
    requires
        a != null
    ensures
        result ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) == n,
        !result ==> exists |i: int| 0 <= i < a.len() && a.index(i) != n
;

proof fn lemma_AllElementsEqual(a: Vec<int>, n: int) -> (result: bool)
    requires
        a != null
    ensures
        result ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) == n,
        !result ==> exists |i: int| 0 <= i < a.len() && a.index(i) != n
{
    false
}

}
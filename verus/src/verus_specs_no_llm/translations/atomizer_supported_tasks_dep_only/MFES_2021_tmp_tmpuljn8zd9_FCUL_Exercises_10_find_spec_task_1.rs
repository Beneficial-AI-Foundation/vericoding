// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_find(a: Vec<int>, key: int) -> index: int
    requires
        a.len() > 0
    ensures
        0 <= index <= a.len(),
        index < a.len() ==> a.index(index) == key
;

proof fn lemma_find(a: Vec<int>, key: int) -> (index: int)
    requires
        a.len() > 0
    ensures
        0 <= index <= a.len(),
        index < a.len() ==> a.index(index) == key
{
    0
}

}
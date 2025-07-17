// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_binSearch(a: Vec<int>, K: int) -> b:bool
    requires
        isSorted(a)
    ensures
        b == exists |i: nat| i < a.len() && a.index(i) == K
;

proof fn lemma_binSearch(a: Vec<int>, K: int) -> (b: bool)
    requires
        isSorted(a)
    ensures
        b == exists |i: nat| i < a.len() && a.index(i) == K
{
    false
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MaxA(a: Vec<int>) -> m: int
    requires
        a.len() > 0
    ensures
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m,
        exists |i: int| 0 <= i < a.len() && a.index(i) == m
;

proof fn lemma_MaxA(a: Vec<int>) -> (m: int)
    requires
        a.len() > 0
    ensures
        forall |i: int| 0 <= i < a.len() ==> a.index(i) <= m,
        exists |i: int| 0 <= i < a.len() && a.index(i) == m
{
    0
}

}
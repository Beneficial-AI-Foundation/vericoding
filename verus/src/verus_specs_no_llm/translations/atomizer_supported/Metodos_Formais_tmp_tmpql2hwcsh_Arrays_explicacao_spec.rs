// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_buscar(a: Vec<int>, x: int) -> r:int
    ensures
        r < 0 ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) != x,
        0 <= r < a.len() ==> a.index(r) == x
;

proof fn lemma_buscar(a: Vec<int>, x: int) -> (r: int)
    ensures
        r < 0 ==> forall |i: int| 0 <= i < a.len() ==> a.index(i) != x,
        0 <= r < a.len() ==> a.index(r) == x
{
    0
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_firste(a: Vec<char>) -> c:int
    ensures
        -1 <= c < a.len(),
        0 <= c < a.len() ==> a.index(c) == 'e' && forall |x: int| 0 <= x < c ==> a.index(x) != 'e',
        c == -1 ==> forall |x: int| 0 <= x < a.len() ==> a.index(x) != 'e'
;

proof fn lemma_firste(a: Vec<char>) -> (c: int)
    ensures
        -1 <= c < a.len(),
        0 <= c < a.len() ==> a.index(c) == 'e' && forall |x: int| 0 <= x < c ==> a.index(x) != 'e',
        c == -1 ==> forall |x: int| 0 <= x < a.len() ==> a.index(x) != 'e'
{
    0
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_firstE(a: Vec<char>) -> x: int
    ensures
        if 'e' in a.index(..) then 0 <= x < a.len() && a.index(x) == 'e' && forall i | 0 <= i < x :: a.index(i) != 'e' else x == -1
;

proof fn lemma_firstE(a: Vec<char>) -> (x: int)
    ensures
        if 'e' in a.index(..) then 0 <= x < a.len() && a.index(x) == 'e' && forall i | 0 <= i < x :: a.index(i) != 'e' else x == -1
{
    0
}

}
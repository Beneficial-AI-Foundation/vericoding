// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_max(s: Vec<nat>) -> a:int
    requires
        s.len() > 0
    ensures
        forall |x: int| 0 <= x < s.len() ==> a >= s.index(x),
        a in s.index(..)
;

proof fn lemma_max(s: Vec<nat>) -> (a: int)
    requires
        s.len() > 0
    ensures
        forall |x: int| 0 <= x < s.len() ==> a >= s.index(x),
        a in s.index(..)
{
    0
}

}
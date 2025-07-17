// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_max(a: Vec<int>) -> max:int
    requires
        a != null
    ensures
        forall |j: int| j >= 0 && j < a.len() ==> max >= a.index(j),
        a.len() > 0 ==> exists |j: int| j >= 0 && j < a.len() && max == a.index(j)
;

proof fn lemma_max(a: Vec<int>) -> (max: int)
    requires
        a != null
    ensures
        forall |j: int| j >= 0 && j < a.len() ==> max >= a.index(j),
        a.len() > 0 ==> exists |j: int| j >= 0 && j < a.len() && max == a.index(j)
{
    0
}

}
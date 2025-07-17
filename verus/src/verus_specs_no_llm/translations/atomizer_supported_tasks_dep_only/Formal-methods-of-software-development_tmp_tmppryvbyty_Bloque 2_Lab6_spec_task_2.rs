// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_maxSeq(v: Seq<int>) -> max:int
    requires
        v.len() >= 1
    ensures
        forall |i: int| 0 <= i < v.len() ==> max >= v.index(i),
        max in v
;

proof fn lemma_maxSeq(v: Seq<int>) -> (max: int)
    requires
        v.len() >= 1
    ensures
        forall |i: int| 0 <= i < v.len() ==> max >= v.index(i),
        max in v
{
    0
}

}
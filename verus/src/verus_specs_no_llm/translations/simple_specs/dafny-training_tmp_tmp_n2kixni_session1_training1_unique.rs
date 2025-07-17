// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<int>) -> bool {
    forall |j: int, k: int|0 <= j < k < a.len() ==> a.index(j) <= a.index(k)
}

spec fn spec_unique(a: Seq<int>) -> b: seq<int>
    requires
        sorted(a)
    ensures
        true
;

proof fn lemma_unique(a: Seq<int>) -> (b: Seq<int>)
    requires
        sorted(a)
    ensures
        true
{
    Seq::empty()
}

}
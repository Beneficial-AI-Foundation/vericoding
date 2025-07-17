// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_PairwiseAddition(a: Vec<int>) -> result: array<int>
    requires
        a != null,
        a.len() % 2 == 0
    ensures
        result != null,
        result.len() == a.len() / 2,
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == a.index(2*i) + a.index(2*i + 1)
;

proof fn lemma_PairwiseAddition(a: Vec<int>) -> (result: Vec<int>)
    requires
        a != null,
        a.len() % 2 == 0
    ensures
        result != null,
        result.len() == a.len() / 2,
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == a.index(2*i) + a.index(2*i + 1)
{
    Vec::new()
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SquareElements(a: Vec<int>) -> squared: array<int>
    ensures
        squared.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> squared.index(i) == a.index(i) * a.index(i)
;

proof fn lemma_SquareElements(a: Vec<int>) -> (squared: Vec<int>)
    ensures
        squared.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> squared.index(i) == a.index(i) * a.index(i)
{
    Vec::new()
}

}
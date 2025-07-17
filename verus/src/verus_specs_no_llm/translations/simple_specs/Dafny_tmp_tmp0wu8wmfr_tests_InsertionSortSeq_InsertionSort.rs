// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSorted(s: Seq<int>) -> bool {
    forall p,q  0<=p<q<.len()s| :: s.index(p)<=s.index(q)
}

spec fn spec_InsertionSort(s: Seq<int>) -> r: seq<int>
    ensures
        multiset(r) == multiset(s),
        IsSorted(r)
;

proof fn lemma_InsertionSort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        multiset(r) == multiset(s),
        IsSorted(r)
{
    Seq::empty()
}

}
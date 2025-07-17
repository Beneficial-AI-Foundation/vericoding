// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_quickSort(Seq: Seq<int>) -> Seq': seq<int>
    ensures
        multiset(Seq) == multiset(Seq')
;

proof fn lemma_quickSort(Seq: Seq<int>) -> (Seq': Seq<int>)
    ensures
        multiset(Seq) == multiset(Seq')
{
    Seq::empty()
}

}
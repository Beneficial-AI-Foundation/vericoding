// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < q.len() ==> q.index(i) <= q.index(j)
}

spec fn spec_MergeSort(a: Vec<int>) -> b: array<int>
    ensures
        b.len() == a.len() && Sorted(b.index(..)) && multiset(a.index(..)) == multiset(b.index(..))
;

proof fn lemma_MergeSort(a: Vec<int>) -> (b: Vec<int>)
    ensures
        b.len() == a.len() && Sorted(b.index(..)) && multiset(a.index(..)) == multiset(b.index(..))
{
    Vec::new()
}

}
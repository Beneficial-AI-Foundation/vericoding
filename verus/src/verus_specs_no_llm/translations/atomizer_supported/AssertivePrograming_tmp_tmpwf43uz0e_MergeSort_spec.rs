// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < q.len() ==> q.index(i) <= q.index(j)
}
spec fn Inv(a: Seq<int>, a1: Seq<int>, a2: Seq<int>, i: nat, mid: nat) -> bool {
    (i <= a1.len()) && (i <= a2.len()) && (i+mid <= a.len()) &&
    (a1.index(..i) == a.index(..i)) && (a2.index(..i) == a.index(mid..(i+mid)))
}
spec fn InvSorted(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
	((i+j > 0 && i < c.len()) ==> (b.index(j + i - 1) <= c.index(i))) &&
	((i+j > 0 && j < d.len()) ==> (b.index(j + i - 1) <= d.index(j))) &&
	Sorted(b.index(..i+j))
}
spec fn InvSubSet(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
	multiset(b.index(..i+j)) == multiset(c.index(..i)) + multiset(d.index(..j))
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
// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall i,j :: 0 <= i <= j < q.len() ==> q.spec_index(i) <= q.spec_index(j)
}
spec fn Inv(a: Seq<int>, a1: Seq<int>, a2: Seq<int>, i: nat, mid: nat) -> bool {
    (i <= a1.len()) && (i <= a2.len()) && (i+mid <= a.len()) &&
    (a1.spec_index(..i) == a.spec_index(..i)) && (a2.spec_index(..i) == a.spec_index(mid..(i+mid)))
}
spec fn InvSorted(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
	((i+j > 0 && i < c.len()) ==> (b.spec_index(j + i - 1) <= c.spec_index(i))) &&
	((i+j > 0 && j < d.len()) ==> (b.spec_index(j + i - 1) <= d.spec_index(j))) &&
	Sorted(b.spec_index(..i+j))
}
spec fn InvSubSet(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
	multiset(b.spec_index(..i+j)) == multiset(c.spec_index(..i)) + multiset(d.spec_index(..j))
}

fn MergeSort(a: Vec<int>) -> (b: Vec<int>)
    ensures
        b.len() == a.len() && Sorted(b.spec_index(..)) && multiset(a.spec_index(..)) == multiset(b.spec_index(..))
{
    return Vec::new();
}

}
// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}
spec fn Inv(a: Seq<int>, a1: Seq<int>, a2: Seq<int>, i: nat, mid: nat) -> bool {
    (i <= a1.len()) and (i <= a2.len()) and (i+mid <= a.len()) and
    (a1[..i] == a[..i]) and (a2[..i] == a[mid..(i+mid)])
}
spec fn InvSorted(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() and j <= d.len() and i + j <= b.len() and
	((i+j > 0 and i < c.len()) ==> (b[j + i - 1] <= c[i])) and
	((i+j > 0 and j < d.len()) ==> (b[j + i - 1] <= d[j])) and
	Sorted(b[..i+j])
}
spec fn InvSubSet(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() and j <= d.len() and i + j <= b.len() and
	multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
}

fn MergeSort(a: Vec<int>) -> (b: Vec<int>)
    ensures b.len() == a.len() and Sorted(b[..]) and multiset(a[..]) == multiset(b[..])
{
}

}
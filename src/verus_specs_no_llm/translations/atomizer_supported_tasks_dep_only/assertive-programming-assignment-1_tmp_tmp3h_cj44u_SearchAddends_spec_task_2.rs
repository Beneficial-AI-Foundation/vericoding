// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}
spec fn HasAddends(q: Seq<int>, x: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < q.len() and q[i] + q[j] == x
}
spec fn AreAddendsIndices(q: Seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j) -> bool {
    q[i] + q[j] == x
}
spec fn HasAddendsInIndicesRange(q: Seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j) -> bool {
    HasAddends(q[i..(j + 1)], x)
}
spec fn LoopInv(q: Seq<int>, x: int, i: nat, j: nat, sum: int) -> bool {
    AreOreredIndices(q, i, j) and
	HasAddendsInIndicesRange(q, x, i, j) and
	AreAddendsIndices(q, sum, i, j)
}

fn FindAddends(q: Seq<int>, x: int) -> i: nat, j: nat
    requires Sorted(q) and HasAddends(q, x)
    ensures i < j < q.len() and q[i]+q[j] == x
{
}

}
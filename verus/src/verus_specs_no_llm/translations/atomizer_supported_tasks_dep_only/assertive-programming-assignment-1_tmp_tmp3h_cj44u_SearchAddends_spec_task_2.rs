// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall i,j :: 0 <= i <= j < q.len() ==> q.spec_index(i) <= q.spec_index(j)
}
spec fn HasAddends(q: Seq<int>, x: int) -> bool {
    exists i,j :: 0 <= i < j < q.len() && q.spec_index(i) + q.spec_index(j) == x
}
spec fn AreAddendsIndices(q: Seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j) -> bool {
    q.spec_index(i) + q.spec_index(j) == x
}
spec fn HasAddendsInIndicesRange(q: Seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j) -> bool {
    HasAddends(q.spec_index(i..(j + 1)), x)
}
spec fn LoopInv(q: Seq<int>, x: int, i: nat, j: nat, sum: int) -> bool {
    AreOreredIndices(q, i, j) &&
	HasAddendsInIndicesRange(q, x, i, j) &&
	AreAddendsIndices(q, sum, i, j)
}

fn FindAddends(q: Seq<int>, x: int) -> (i: nat, j: nat)
    requires
        Sorted(q) && HasAddends(q, x)
    ensures
        i < j < q.len() && q.spec_index(i)+q.spec_index(j) == x
{
    return (0, 0);
}

}
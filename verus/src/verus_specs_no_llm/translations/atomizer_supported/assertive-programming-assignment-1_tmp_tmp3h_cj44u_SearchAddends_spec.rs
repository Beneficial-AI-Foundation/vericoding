// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < q.len() ==> q.index(i) <= q.index(j)
}
spec fn HasAddends(q: Seq<int>, x: int) -> bool {
    exists |i: int, j: int| 0 <= i < j < q.len() && q.index(i) + q.index(j) == x
}
spec fn AreAddendsIndices(q: Seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j) -> bool {
    q.index(i) + q.index(j) == x
}
spec fn HasAddendsInIndicesRange(q: Seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j) -> bool {
    HasAddends(q.index(i..(j + 1)), x)
}
spec fn LoopInv(q: Seq<int>, x: int, i: nat, j: nat, sum: int) -> bool {
    AreOreredIndices(q, i, j) &&
	HasAddendsInIndicesRange(q, x, i, j) &&
	AreAddendsIndices(q, sum, i, j)
}

spec fn spec_Main()
{
}


// ATOM 

predicate Sorted(q: Seq<int>, j: : 0 <= i <= j < |q| ==> q[i] <= q[j] 
}


// ATOM 

predicate HasAddends(q: seq<int>, x: int)
{
	exists i, j: : 0 <= i < j < |q| && q[i] + q[j] == x
}


// SPEC 

method FindAddends(q: seq<int>, x: int) -> i: nat, j: nat
    requires
        Sorted(q) && HasAddends(q, x)
    ensures
        i < j < q.len() && q.index(i)+q.index(j) == x
;

proof fn lemma_Main()
{
}


// ATOM 

predicate Sorted(q: Seq<int>, j: : 0 <= i <= j < |q| ==> q[i] <= q[j] 
}


// ATOM 

predicate HasAddends(q: seq<int>, x: int)
{
	exists i, j: : 0 <= i < j < |q| && q[i] + q[j] == x
}


// SPEC 

method FindAddends(q: seq<int>, x: int) -> (i: nat, j: nat)
    requires
        Sorted(q) && HasAddends(q, x)
    ensures
        i < j < q.len() && q.index(i)+q.index(j) == x
{
    (0, 0)
}

}
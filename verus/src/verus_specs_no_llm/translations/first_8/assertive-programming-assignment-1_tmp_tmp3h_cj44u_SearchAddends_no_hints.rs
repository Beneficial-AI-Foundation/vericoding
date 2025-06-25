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

fn Main()
{
	var q: = [1, 2, 4, 5, 6, 7, 10, 23];
	var i, j: = FindAddends(q, 10);
	print "Searching for addends of 10 in q == [1, 2, 4, 5, 6, 7, 10, 23]: \n";
	print "Found that q[";
	print i;
	print "] + q[";
	print j;
	print "] == ";
	print q[i];
	print " + ";
	print q[j];
	print " == 10";
}
//ATOM
predicate Sorted(q: seq<int>)
{
	forall i, j: : 0 <= i <= j < |q| ==> q[i] <= q[j] 
}
//ATOM
predicate HasAddends(q: seq<int>, x: int)
{
	exists i, j: : 0 <= i < j < |q| && q[i] + q[j] == x
}
//SPEC
method FindAddends(q: seq<int>, x: int) -> (i: nat, j: nat)
    requires
        Sorted(q) && HasAddends(q, x)
    ensures
        i < j < q.len() && q.spec_index(i)+q.spec_index(j) == x
{
    return (0, 0);
}

}
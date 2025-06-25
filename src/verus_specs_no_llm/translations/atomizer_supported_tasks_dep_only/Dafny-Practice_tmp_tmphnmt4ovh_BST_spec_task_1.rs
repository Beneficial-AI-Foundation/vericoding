// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}
spec fn Ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}
spec fn NoDuplicates(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] != q[j]
}

fn Main() {
}


// SPEC 

method PrintTreeNumbersInorder(t: Tree)
{
}


// ATOM 

function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
}


// ATOM 

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}


// ATOM 

predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}


// ATOM 

function Inorder(t: Tree): seq<int>
{
	match t {
		case Empty => []
		case Node(n', nt1, nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}


// ATOM 

predicate Ascending(q: Seq<int>, j: : 0 <= i < j < |q| ==> q[i] < q[j]
}


// ATOM 

predicate NoDuplicates(q: seq<int>) { forall i, j: : 0 <= i < j < |q| ==> q[i] != q[j] }

/*
	Goal: Implement correctly, clearly. No need to document the proof obligations.
*/


/*
	Goal: Implement correctly, clearly. No need to document the proof obligations.
*/
// SPEC 
method BuildBST(q: Seq<int>) -> (t: Tree)
    requires NoDuplicates(q)
    ensures BST(t) and NumbersInTree(t) == NumbersInSequence(q)
{
}

}
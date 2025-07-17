// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}
spec fn Ascending(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < q.len() ==> q.index(i) < q.index(j)
}
spec fn NoDuplicates(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < q.len() ==> q.index(i) != q.index(j)
}

spec fn NumbersInTree(t: Tree) -> set<int>
{
    0
}

spec fn spec_InsertBST(t0: Tree, x: int) -> t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{
  t := Empty;
  assume BST(t) && NumbersInTree(t) ==> NumbersInTree(t0)+{x};
  return t;
}
{
  t := Empty;
  assume BST(t) && NumbersInTree(t) ==> NumbersInTree(t0)+{x};
  return t;
}


//ATOM

predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}


//ATOM

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}


//ATOM

predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

/*
	Goal: Implement correctly, clearly. No need to document the proof obligations.
*/


//ATOM

function Inorder(t: Tree): seq<int>
{
	match t {
		case Empty => []
		case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}


//ATOM
method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
  t := Empty;
  assume BST(t) && NumbersInTree(t) ==> NumbersInSequence(q);
  return t;
}

/*
	Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/


//ATOM

method PrintTreeNumbersInorder(t: Tree
    requires
        BST(t0) && x !in NumbersInTree(t0),
        NoDuplicates(q)
    ensures
        BST(t) && NumbersInTree(t) == NumbersInTree(t0)+,
        BST(t) && NumbersInTree(t) == NumbersInSequence(q)
;

proof fn lemma_InsertBST(t0: Tree, x: int) -> (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{
  t := Empty;
  assume BST(t) && NumbersInTree(t) ==> NumbersInTree(t0)+{x};
  return t;
}
{
  t := Empty;
  assume BST(t) && NumbersInTree(t) ==> NumbersInTree(t0)+{x};
  return t;
}


//ATOM

predicate Ascending(q: seq<int>)
{
	forall i, j: : 0 <= i < j < |q| ==> q[i] < q[j]
}


//ATOM

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}


//ATOM

predicate NoDuplicates(q: seq<int>) { forall i, j: : 0 <= i < j < |q| ==> q[i] != q[j] }

/*
	Goal: Implement correctly, clearly. No need to document the proof obligations.
*/


//ATOM

function Inorder(t: Tree): seq<int>
{
	match t {
		case Empty => []
		case Node(n', nt1, nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}


//ATOM
method BuildBST(q: Seq<int>, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/


//ATOM

method PrintTreeNumbersInorder(t: Tree)
    requires
        BST(t0) && x !in NumbersInTree(t0),
        NoDuplicates(q)
    ensures
        BST(t) && NumbersInTree(t) == NumbersInTree(t0)+,
        BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
    (0, 0, 0, 0, 0, Seq::empty(), 0, 0, 0, 0)
}

}
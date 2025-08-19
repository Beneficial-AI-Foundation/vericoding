//ATOM

datatype Tree = Empty | Node(int,Tree,Tree)

//ATOM

function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
}

//ATOM

method InsertBST(t0: Tree, x: int) returns (t: Tree)
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

predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}


// SPEC
method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
}

/*
	Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/
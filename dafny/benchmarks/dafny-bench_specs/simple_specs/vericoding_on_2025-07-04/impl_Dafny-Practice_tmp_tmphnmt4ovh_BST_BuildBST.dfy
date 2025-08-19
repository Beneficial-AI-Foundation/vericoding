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
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{
  t := Empty;
  assume BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x};
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


//IMPL BuildBST
method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
	t := Empty;
	
	for i := 0 to |q|
		invariant BST(t)
		invariant NumbersInTree(t) == NumbersInSequence(q[..i])
	{
		assert q[i] in NumbersInSequence(q[..i+1]);
		assert q[i] !in NumbersInSequence(q[..i]) by {
			NoDuplicatesImpliesNotInPrefix(q, i);
		}
		assert q[i] !in NumbersInTree(t);
		
		t := InsertBST(t, q[i]);
		
		assert NumbersInTree(t) == NumbersInSequence(q[..i]) + {q[i]};
		NumbersInSequenceExtendLemma(q, i);
		assert NumbersInSequence(q[..i+1]) == NumbersInSequence(q[..i]) + {q[i]};
	}
	
	assert q[..|q|] == q;
	assert NumbersInTree(t) == NumbersInSequence(q);
}

lemma NoDuplicatesImpliesNotInPrefix(q: seq<int>, i: int)
	requires 0 <= i < |q|
	requires NoDuplicates(q)
	ensures q[i] !in NumbersInSequence(q[..i])
{
	if q[i] in NumbersInSequence(q[..i]) {
		var j :| 0 <= j < i && q[j] == q[i];
		assert j < i;
		assert q[j] == q[i];
		assert false;
	}
}

lemma NumbersInSequenceExtendLemma(q: seq<int>, i: int)
	requires 0 <= i < |q|
	ensures NumbersInSequence(q[..i+1]) == NumbersInSequence(q[..i]) + {q[i]}
{
	assert q[..i+1] == q[..i] + [q[i]];
}

/*
	Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/
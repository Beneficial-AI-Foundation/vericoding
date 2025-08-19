//ATOM

datatype Tree = Empty | Node(int,Tree,Tree)

//ATOM

function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
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

//IMPL InsertBST
/* code modified by LLM (iteration 4): Main method implementation */
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0) + {x}
{
	match t0 {
		case Empty => 
			t := Node(x, Empty, Empty);
			
		case Node(n, left, right) =>
			if x < n {
				var newLeft := InsertBST(left, x);
				t := Node(n, newLeft, right);
				/* code modified by LLM (iteration 4): Added lemma call for left insertion */
				InsertLeftPreservesBST(left, right, n, x, newLeft);
			} else {
				var newRight := InsertBST(right, x);
				t := Node(n, left, newRight);
				/* code modified by LLM (iteration 4): Added lemma call for right insertion */
				InsertRightPreservesBST(left, right, n, x, newRight);
			}
	}
}

/* code modified by LLM (iteration 4): Helper lemma for left insertion */
lemma InsertLeftPreservesBST(left: Tree, right: Tree, n: int, x: int, newLeft: Tree)
	requires BST(Node(n, left, right))
	requires BST(newLeft)
	requires x !in NumbersInTree(Node(n, left, right))
	requires x < n
	requires NumbersInTree(newLeft) == NumbersInTree(left) + {x}
	ensures BST(Node(n, newLeft, right))
	ensures NumbersInTree(Node(n, newLeft, right)) == NumbersInTree(Node(n, left, right)) + {x}
{
	var oldTree := Node(n, left, right);
	var newTree := Node(n, newLeft, right);
	
	/* code modified by LLM (iteration 4): Establish key properties */
	assert Inorder(newTree) == Inorder(newLeft) + [n] + Inorder(right);
	assert Inorder(oldTree) == Inorder(left) + [n] + Inorder(right);
	
	/* code modified by LLM (iteration 4): Prove BST property holds */
	assert BST(oldTree);
	assert forall i :: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n;
	assert forall i :: 0 <= i < |Inorder(right)| ==> Inorder(right)[i] > n;
	assert x < n;
	
	/* code modified by LLM (iteration 4): Use helper to prove ascending */
	ProveAscendingAfterLeftInsert(Inorder(left), Inorder(right), n, x, Inorder(newLeft));
}

/* code modified by LLM (iteration 4): Helper lemma for right insertion */
lemma InsertRightPreservesBST(left: Tree, right: Tree, n: int, x: int, newRight: Tree)
	requires BST(Node(n, left, right))
	requires BST(newRight)
	requires x !in NumbersInTree(Node(n, left, right))
	requires x > n
	requires NumbersInTree(newRight) == NumbersInTree(right) + {x}
	ensures BST(Node(n, left, newRight))
	ensures NumbersInTree(Node(n, left, newRight)) == NumbersInTree(Node(n, left, right)) + {x}
{
	var oldTree := Node(n, left, right);
	var newTree := Node(n, left, newRight);
	
	/* code modified by LLM (iteration 4): Establish key properties */
	assert Inorder(newTree) == Inorder(left) + [n] + Inorder(newRight);
	assert Inorder(oldTree) == Inorder(left) + [n] + Inorder(right);
	
	/* code modified by LLM (iteration 4): Prove BST property holds */
	assert BST(oldTree);
	assert forall i :: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n;
	assert forall i :: 0 <= i < |Inorder(right)| ==> Inorder(right)[i] > n;
	assert x > n;
	
	/* code modified by LLM (iteration 4): Use helper to prove ascending */
	ProveAscendingAfterRightInsert(Inorder(left), Inorder(right), n, x, Inorder(newRight));
}

/* code modified by LLM (iteration 4): Prove ascending property after left insertion */
lemma ProveAscendingAfterLeftInsert(leftSeq: seq<int>, rightSeq: seq<int>, n: int, x: int, newLeftSeq: seq<int>)
	requires Ascending(leftSeq + [n] + rightSeq)
	requires Ascending(newLeftSeq)
	requires x < n
	requires x !in (set y | y in leftSeq + [n] + rightSeq)
	requires set y | y in newLeftSeq == set y | y in leftSeq + {x}
	requires forall i :: 0 <= i < |leftSeq| ==> leftSeq[i] < n
	requires forall i :: 0 <= i < |rightSeq| ==> rightSeq[i] > n
	ensures Ascending(newLeftSeq + [n] + rightSeq)
{
	var newSeq := newLeftSeq + [n] + rightSeq;
	
	/* code modified by LLM (iteration 4): Prove all elements in newLeftSeq are < n */
	forall i | 0 <= i < |newLeftSeq|
		ensures newLeftSeq[i] < n
	{
		assert newLeftSeq[i] in set y | y in newLeftSeq;
		assert newLeftSeq[i] in set y | y in leftSeq + {x};
		if newLeftSeq[i] == x {
			assert x < n;
		} else {
			assert newLeftSeq[i] in set y | y in leftSeq;
			assert exists j :: 0 <= j < |leftSeq| && leftSeq[j] == newLeftSeq[i];
		}
	}
	
	/* code modified by LLM (iteration 4): Prove ascending property */
	forall i, j | 0 <= i < j < |newSeq|
		ensures newSeq[i] < newSeq[j]
	{
		if j < |newLeftSeq| {
			assert Ascending(newLeftSeq);
		} else if i < |newLeftSeq| && j == |newLeftSeq| {
			assert newSeq[i] == newLeftSeq[i] && newSeq[j] == n;
		} else if i < |newLeftSeq| && j > |newLeftSeq| {
			assert newSeq[i] == newLeftSeq[i] && newSeq[j] == rightSeq[j - |newLeftSeq| - 1];
			assert newLeftSeq[i] < n && rightSeq[j - |newLeftSeq| - 1] > n;
		} else if i == |newLeftSeq| && j > |newLeftSeq| {
			assert newSeq[i] == n && newSeq[j] == rightSeq[j - |newLeftSeq| - 1];
			assert n < rightSeq[j - |newLeftSeq| - 1];
		} else {
			assert i > |newLeftSeq| && j > |newLeftSeq|;
			assert Ascending(rightSeq);
		}
	}
}

/* code modified by LLM (iteration 4): Prove ascending property after right insertion */
lemma ProveAscendingAfterRightInsert(leftSeq: seq<int>, rightSeq: seq<int>, n: int, x: int, newRightSeq: seq<int>)
	requires Ascending(leftSeq + [n] + rightSeq)
	requires Ascending(newRightSeq)
	requires x > n
	requires x !in (set y | y in leftSeq + [n] + rightSeq)
	requires set y | y in newRightSeq == set y | y in rightSeq + {x}
	requires forall i :: 0 <= i < |leftSeq| ==> leftSeq[i] < n
	requires forall i :: 0 <= i < |rightSeq| ==> rightSeq[i] > n
	ensures Ascending(leftSeq + [n] + newRightSeq)
{
	var newSeq := leftSeq + [n] + newRightSeq;
	
	/* code modified by LLM (iteration 4): Prove all elements in newRightSeq are > n */
	forall i | 0 <= i < |newRightSeq|
		ensures newRightSeq[i] > n
	{
		assert newRightSeq[i] in set y | y in newRightSeq;
		assert newRightSeq[i] in set y | y in rightSeq + {x};
		if newRightSeq[i] == x {
			assert x > n;
		} else {
			assert newRightSeq[i] in set y | y in rightSeq;
			assert exists j :: 0 <= j < |rightSeq| && rightSeq[j] == newRightSeq[i];
		}
	}
	
	/* code modified by LLM (iteration 4): Prove ascending property */
	forall i, j | 0 <= i < j < |newSeq|
		ensures newSeq[i] < newSeq[j]
	{
		if j < |leftSeq| {
			assert Ascending(leftSeq);
		} else if i < |leftSeq| && j == |leftSeq| {
			assert newSeq[i] == leftSeq[i] && newSeq[j] == n;
			assert leftSeq[i] < n;
		} else if i < |leftSeq| && j > |leftSeq| {
			assert newSeq[i] == leftSeq[i] && newSeq[j] == newRightSeq[j - |leftSeq| - 1];
			assert leftSeq[i] < n && newRightSeq[j - |leftSeq| - 1] > n;
		} else if i == |leftSeq| && j > |leftSeq| {
			assert newSeq[i] == n && newSeq[j] == newRightSeq[j - |leftSeq| - 1];
			assert n < newRightSeq[j - |leftSeq| - 1];
		} else {
			assert i > |leftSeq| && j > |leftSeq|;
			assert Ascending(newRightSeq);
		}
	}
}
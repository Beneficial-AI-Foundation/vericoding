// ATOM 
datatype Tree = Empty | Node(int,Tree,Tree)

//IMPL Main
method Main() {
}

//IMPL PrintTreeNumbersInorder
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
		case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}

// ATOM 
predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

// ATOM 
predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

//IMPL BuildBST
method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
	t := Empty;
	/* code modified by LLM (iteration 4): simplified loop with correct invariants */
	var i := 0;
	while i < |q|
		invariant 0 <= i <= |q|
		invariant BST(t)
		invariant NumbersInTree(t) == NumbersInSequence(q[..i])
	{
		/* code modified by LLM (iteration 4): prove element not already in tree */
		assert q[i] !in NumbersInSequence(q[..i]) by {
			if q[i] in NumbersInSequence(q[..i]) {
				var j :| 0 <= j < i && q[j] == q[i];
				assert false;
			}
		}
		t := InsertBST(t, q[i]);
		i := i + 1;
	}
}

//IMPL InsertBST
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{
	match t0 
	{
		case Empty => 
			t := Node(x, Empty, Empty);

		case Node(i, left, right) => 
		{
			if x < i
			{
				/* code modified by LLM (iteration 4): establish subtree properties */
				assert BST(left) by { LemmaBinarySearchSubtree(i, left, right); }
				assert x !in NumbersInTree(left) by {
					if x in NumbersInTree(left) {
						assert x in NumbersInTree(t0);
						assert false;
					}
				}
				
				var newLeft := InsertBST(left, x);
				t := Node(i, newLeft, right);
				
				/* code modified by LLM (iteration 4): prove BST and NumbersInTree properties */
				assert NumbersInTree(t) == NumbersInTree(t0) + {x} by {
					assert NumbersInTree(t) == NumbersInTree(newLeft) + {i} + NumbersInTree(right);
					assert NumbersInTree(newLeft) == NumbersInTree(left) + {x};
					assert NumbersInTree(t0) == NumbersInTree(left) + {i} + NumbersInTree(right);
				}
				
				assert BST(t) by {
					LemmaInsertLeftPreservesBST(i, left, right, newLeft, x);
				}
			}
			else
			{
				/* code modified by LLM (iteration 4): establish subtree properties */
				assert BST(right) by { LemmaBinarySearchSubtree(i, left, right); }
				assert x !in NumbersInTree(right) by {
					if x in NumbersInTree(right) {
						assert x in NumbersInTree(t0);
						assert false;
					}
				}
				
				var newRight := InsertBST(right, x);
				t := Node(i, left, newRight);
				
				/* code modified by LLM (iteration 4): prove BST and NumbersInTree properties */
				assert NumbersInTree(t) == NumbersInTree(t0) + {x} by {
					assert NumbersInTree(t) == NumbersInTree(left) + {i} + NumbersInTree(newRight);
					assert NumbersInTree(newRight) == NumbersInTree(right) + {x};
					assert NumbersInTree(t0) == NumbersInTree(left) + {i} + NumbersInTree(right);
				}
				
				assert BST(t) by {
					LemmaInsertRightPreservesBST(i, left, right, newRight, x);
				}
			}
		}
	}
}

// ATOM 
lemma	LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures BST(left) && BST(right)
{
	var qleft, qright := Inorder(left), Inorder(right);
	var q := qleft+[n]+qright;
}

// ATOM 
lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
	requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
	requires Ascending(q1)
	ensures Ascending(q2)
{}

/* code modified by LLM (iteration 4): simplified lemma for left insertion */
lemma LemmaInsertLeftPreservesBST(i: int, left: Tree, right: Tree, newLeft: Tree, x: int)
	requires BST(Node(i, left, right))
	requires x < i
	requires BST(newLeft)
	requires NumbersInTree(newLeft) == NumbersInTree(left) + {x}
	requires x !in NumbersInTree(left)
	ensures BST(Node(i, newLeft, right))
{
	var oldInorder := Inorder(left) + [i] + Inorder(right);
	var newInorder := Inorder(newLeft) + [i] + Inorder(right);
	
	assert Ascending(oldInorder);
	assert Ascending(Inorder(newLeft));
	assert Ascending(Inorder(right));
	
	/* code modified by LLM (iteration 4): prove ordering properties */
	assert forall k :: k in NumbersInTree(left) ==> k < i by {
		LemmaBSTOrdering(Node(i, left, right));
	}
	assert x < i;
	assert forall k :: k in NumbersInTree(right) ==> k > i by {
		LemmaBSTOrdering(Node(i, left, right));
	}
	
	assert Ascending(newInorder) by {
		LemmaAscendingConcatenation(Inorder(newLeft), [i], Inorder(right), x, i);
	}
}

/* code modified by LLM (iteration 4): simplified lemma for right insertion */
lemma LemmaInsertRightPreservesBST(i: int, left: Tree, right: Tree, newRight: Tree, x: int)
	requires BST(Node(i, left, right))
	requires x > i
	requires BST(newRight)
	requires NumbersInTree(newRight) == NumbersInTree(right) + {x}
	requires x !in NumbersInTree(right)
	ensures BST(Node(i, left, newRight))
{
	var oldInorder := Inorder(left) + [i] + Inorder(right);
	var newInorder := Inorder(left) + [i] + Inorder(newRight);
	
	assert Ascending(oldInorder);
	assert Ascending(Inorder(left));
	assert Ascending(Inorder(newRight));
	
	/* code modified by LLM (iteration 4): prove ordering properties */
	assert forall k :: k in NumbersInTree(left) ==> k < i by {
		LemmaBSTOrdering(Node(i, left, right));
	}
	assert forall k :: k in NumbersInTree(right) ==> k > i by {
		LemmaBSTOrdering(Node(i, left, right));
	}
	assert x > i;
	
	assert Ascending(newInorder) by {
		LemmaAscendingConcatenationRight(Inorder(left), [i], Inorder(newRight), x, i);
	}
}

/* code modified by LLM (iteration 4): helper lemma for BST ordering properties */
lemma LemmaBSTOrdering(tree: Tree)
	requires BST(tree)
	requires tree.Node?
	ensures forall k :: k in NumbersInTree(tree.left) ==> k < tree.n
	ensures forall k :: k in NumbersInTree(tree.right) ==> k > tree.n
{
	var inorderSeq := Inorder(tree);
	var leftSeq := Inorder(tree.left);
	var rightSeq := Inorder(tree.right);
	
	assert inorderSeq == leftSeq + [tree.n] + rightSeq;
	assert Ascending(inorderSeq);
	
	forall k | k in NumbersInTree(tree.left)
		ensures k < tree.n
	{
		assert k in NumbersInSequence(leftSeq);
		var idx :| 0 <= idx < |leftSeq| && leftSeq[idx] == k;
		assert inorderSeq[idx] == k;
		assert inorderSeq[|leftSeq|] == tree.n;
		assert idx < |leftSeq|;
	}
	
	forall k | k in NumbersInTree(tree.right)
		ensures k > tree.n
	{
		assert k in NumbersInSequence(rightSeq);
		var idx :| 0 <= idx < |rightSeq| && rightSeq[idx] == k;
		var globalIdx := |leftSeq| + 1 + idx;
		assert inorderSeq[globalIdx] == k;
		assert inorderSeq[|leftSeq|] == tree.n;
		assert |leftSeq| < globalIdx;
	}
}

/* code modified by LLM (iteration 4): helper lemma for concatenation ordering */
lemma LemmaAscendingConcatenation(s1: seq<int>, s2: seq<int>, s3: seq<int>, x: int, pivot: int)
	requires Ascending(s1)
	requires Ascending(s2)
	requires Ascending(s3)
	requires |s2| == 1 && s2[0] == pivot
	requires forall k :: k in s1 ==> k < pivot
	requires forall k :: k in s3 ==> k > pivot
	requires x < pivot
	requires x in s1
	ensures Ascending(s1 + s2 + s3)
{
	var result := s1 + s2 + s3;
	forall i, j | 0 <= i < j < |result|
		ensures result[i] < result[j]
	{
		if i < |s1| && j < |s1| {
			assert result[i] < result[j];
		} else if i < |s1| && j == |s1| {
			assert result[i] in s1;
			assert result[j] == pivot;
		} else if i < |s1| && j > |s1| {
			assert result[i] in s1;
			assert result[j] in s3;
		} else if i == |s1| && j > |s1| {
			assert result[i] == pivot;
			assert result[j] in s3;
		} else {
			assert i > |s1| && j > |s1|;
			assert result[i] in s3;
			assert result[j] in s3;
		}
	}
}

/* code modified by LLM (iteration 4): helper lemma for right concatenation ordering */
lemma LemmaAscendingConcatenationRight(s1: seq<int>, s2: seq<int>, s3: seq<int>, x: int, pivot: int)
	requires Ascending(s1)
	requires Ascending(s2)
	requires Ascending(s3)
	requires |s2| == 1 && s2[0] == pivot
	requires forall k :: k in s1 ==> k < pivot
	requires forall k :: k in s3 ==> k > pivot
	requires x > pivot
	requires x in s3
	ensures Ascending(s1 + s2 + s3)
{
	var result := s1 + s2 + s3;
	forall i, j | 0 <= i < j < |result|
		ensures result[i] < result[j]
	{
		if i < |s1| && j < |s1| {
			assert result[i] < result[j];
		} else if i < |s1| && j == |s1| {
			assert result[i] in s1;
			assert result[j] == pivot;
		} else if i < |s1| && j > |s1| {
			assert result[i] in s1;
			assert result[j] in s3;
		} else if i == |s1| && j > |s1| {
			assert result[i] == pivot;
			assert result[j] in s3;
		} else {
			assert i > |s1| && j > |s1|;
			assert result[i] in s3;
			assert result[j] in s3;
		}
	}
}
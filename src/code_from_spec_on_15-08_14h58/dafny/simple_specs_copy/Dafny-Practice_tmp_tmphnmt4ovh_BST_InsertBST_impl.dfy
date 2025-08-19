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

/* code modified by LLM (iteration 4): Added helper lemma to prove subsequence properties */
lemma SubsequenceAscending(seq1: seq<int>, seq2: seq<int>, full: seq<int>)
	requires full == seq1 + seq2
	requires Ascending(full)
	ensures Ascending(seq1) && Ascending(seq2)
{
	// Prove seq1 is ascending
	forall i, j | 0 <= i < j < |seq1|
		ensures seq1[i] < seq1[j]
	{
		assert seq1[i] == full[i];
		assert seq1[j] == full[j];
		assert 0 <= i < j < |full|;
	}
	
	// Prove seq2 is ascending
	forall i, j | 0 <= i < j < |seq2|
		ensures seq2[i] < seq2[j]
	{
		assert seq2[i] == full[|seq1| + i];
		assert seq2[j] == full[|seq1| + j];
		assert 0 <= |seq1| + i < |seq1| + j < |full|;
	}
}

/* code modified by LLM (iteration 4): Fixed three-part subsequence lemma to properly prove middle is ascending */
lemma ThreePartSubsequenceAscending(seq1: seq<int>, middle: seq<int>, seq3: seq<int>, full: seq<int>)
	requires full == seq1 + middle + seq3
	requires Ascending(full)
	ensures Ascending(seq1) && Ascending(middle) && Ascending(seq3)
{
	// Prove seq1 is ascending
	forall i, j | 0 <= i < j < |seq1|
		ensures seq1[i] < seq1[j]
	{
		assert seq1[i] == full[i];
		assert seq1[j] == full[j];
		assert 0 <= i < j < |full|;
	}
	
	// Prove middle is ascending
	forall i, j | 0 <= i < j < |middle|
		ensures middle[i] < middle[j]
	{
		assert middle[i] == full[|seq1| + i];
		assert middle[j] == full[|seq1| + j];
		assert 0 <= |seq1| + i < |seq1| + j < |full|;
	}
	
	// Prove seq3 is ascending
	forall i, j | 0 <= i < j < |seq3|
		ensures seq3[i] < seq3[j]
	{
		assert seq3[i] == full[|seq1| + |middle| + i];
		assert seq3[j] == full[|seq1| + |middle| + j];
		assert 0 <= |seq1| + |middle| + i < |seq1| + |middle| + j < |full|;
	}
}

/* code modified by LLM (iteration 4): Improved subtree BST lemma */
lemma SubtreesOfBSTAreBST(t: Tree)
	requires BST(t)
	ensures match t {
		case Empty => true
		case Node(n, left, right) => BST(left) && BST(right)
	}
{
	match t {
		case Empty => 
		case Node(n, left, right) =>
			var leftSeq := Inorder(left);
			var rightSeq := Inorder(right);
			var fullSeq := leftSeq + [n] + rightSeq;
			
			assert Inorder(t) == fullSeq;
			assert Ascending(fullSeq);
			
			ThreePartSubsequenceAscending(leftSeq, [n], rightSeq, fullSeq);
	}
}

/* code modified by LLM (iteration 4): Added helper lemma to prove element not in tree implies not in subtrees */
lemma ElementNotInSubtrees(t: Tree, x: int)
	requires x !in NumbersInTree(t)
	ensures match t {
		case Empty => true
		case Node(n, left, right) => x !in NumbersInTree(left) && x !in NumbersInTree(right)
	}
{
	match t {
		case Empty =>
		case Node(n, left, right) =>
			assert NumbersInTree(t) == NumbersInTree(left) + {n} + NumbersInTree(right);
	}
}

/* code modified by LLM (iteration 4): Added helper lemma to prove BST ordering properties */
lemma BSTOrderingProperties(t: Tree)
	requires BST(t)
	ensures match t {
		case Empty => true
		case Node(n, left, right) => 
			(forall x :: x in NumbersInTree(left) ==> x < n) &&
			(forall x :: x in NumbersInTree(right) ==> n < x)
	}
{
	match t {
		case Empty =>
		case Node(n, left, right) =>
			var leftSeq := Inorder(left);
			var rightSeq := Inorder(right);
			var fullSeq := leftSeq + [n] + rightSeq;
			
			// Prove left elements are less than n
			forall x | x in NumbersInTree(left)
				ensures x < n
			{
				assert x in NumbersInSequence(leftSeq);
				var i :| 0 <= i < |leftSeq| && leftSeq[i] == x;
				assert fullSeq[i] == x;
				assert fullSeq[|leftSeq|] == n;
				assert i < |leftSeq|;
				assert fullSeq[i] < fullSeq[|leftSeq|];
			}
			
			// Prove right elements are greater than n
			forall x | x in NumbersInTree(right)
				ensures n < x
			{
				assert x in NumbersInSequence(rightSeq);
				var i :| 0 <= i < |rightSeq| && rightSeq[i] == x;
				assert fullSeq[|leftSeq| + 1 + i] == x;
				assert fullSeq[|leftSeq|] == n;
				assert |leftSeq| < |leftSeq| + 1 + i;
				assert fullSeq[|leftSeq|] < fullSeq[|leftSeq| + 1 + i];
			}
	}
}

/* code modified by LLM (iteration 4): Added helper lemma to prove new sequence is ascending */
lemma ProveNewSequenceAscending(newSeq: seq<int>, leftPart: seq<int>, middlePart: seq<int>, rightPart: seq<int>)
	requires newSeq == leftPart + middlePart + rightPart
	requires Ascending(leftPart) && Ascending(middlePart) && Ascending(rightPart)
	requires forall i, j :: 0 <= i < |leftPart| && 0 <= j < |middlePart| ==> leftPart[i] < middlePart[j]
	requires forall i, j :: 0 <= i < |middlePart| && 0 <= j < |rightPart| ==> middlePart[i] < rightPart[j]
	ensures Ascending(newSeq)
{
	forall i, j | 0 <= i < j < |newSeq|
		ensures newSeq[i] < newSeq[j]
	{
		if j < |leftPart| {
			// Both in left part
			assert Ascending(leftPart);
		} else if i >= |leftPart| + |middlePart| {
			// Both in right part
			var ri := i - |leftPart| - |middlePart|;
			var rj := j - |leftPart| - |middlePart|;
			assert newSeq[i] == rightPart[ri];
			assert newSeq[j] == rightPart[rj];
			assert 0 <= ri < rj < |rightPart|;
			assert Ascending(rightPart);
		} else if |leftPart| <= i < |leftPart| + |middlePart| && |leftPart| + |middlePart| <= j {
			// i in middle, j in right
			var mi := i - |leftPart|;
			var rj := j - |leftPart| - |middlePart|;
			assert newSeq[i] == middlePart[mi];
			assert newSeq[j] == rightPart[rj];
		} else if i < |leftPart| && |leftPart| + |middlePart| <= j {
			// i in left, j in right
			var rj := j - |leftPart| - |middlePart|;
			assert newSeq[i] == leftPart[i];
			assert newSeq[j] == rightPart[rj];
			// Need to show leftPart[i] < rightPart[rj]
			if |middlePart| > 0 {
				assert leftPart[i] < middlePart[0];
				assert middlePart[|middlePart| - 1] < rightPart[rj];
				if |middlePart| == 1 {
					assert middlePart[0] == middlePart[|middlePart| - 1];
				} else {
					assert middlePart[0] < middlePart[|middlePart| - 1];
				}
			}
		} else if i < |leftPart| && |leftPart| <= j < |leftPart| + |middlePart| {
			// i in left, j in middle
			var mj := j - |leftPart|;
			assert newSeq[i] == leftPart[i];
			assert newSeq[j] == middlePart[mj];
		} else if |leftPart| <= i < j < |leftPart| + |middlePart| {
			// Both in middle
			var mi := i - |leftPart|;
			var mj := j - |leftPart|;
			assert newSeq[i] == middlePart[mi];
			assert newSeq[j] == middlePart[mj];
			assert 0 <= mi < mj < |middlePart|;
			assert Ascending(middlePart);
		}
	}
}

/* code modified by LLM (iteration 4): Completely rewritten BST preservation lemma with proper sequence construction */
lemma InsertPreservesBST(t0: Tree, x: int, t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	requires match t0 {
		case Empty => t == Node(x, Empty, Empty)
		case Node(n, left, right) => 
			if x < n then 
				exists newLeft :: BST(newLeft) && NumbersInTree(newLeft) == NumbersInTree(left) + {x} && t == Node(n, newLeft, right)
			else 
				exists newRight :: BST(newRight) && NumbersInTree(newRight) == NumbersInTree(right) + {x} && t == Node(n, left, newRight)
	}
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0) + {x}
{
	match t0 {
		case Empty =>
			assert Inorder(t) == [x];
			assert Ascending([x]);
		case Node(n, left, right) =>
			BSTOrderingProperties(t0);
			
			if x < n {
				var newLeft :| BST(newLeft) && NumbersInTree(newLeft) == NumbersInTree(left) + {x} && t == Node(n, newLeft, right);
				BSTOrderingProperties(newLeft);
				
				var newLeftSeq := Inorder(newLeft);
				var rightSeq := Inorder(right);
				var newSeq := newLeftSeq + [n] + rightSeq;
				
				assert Inorder(t) == newSeq;
				assert NumbersInTree(t) == NumbersInTree(t0) + {x};
				
				// Establish that the new sequence is ascending
				assert BST(newLeft);
				assert Ascending(newLeftSeq);
				assert BST(right);
				assert Ascending(rightSeq);
				
				// Prove ordering between parts
				forall i, j | 0 <= i < |newLeftSeq| && 0 <= j < 1
					ensures newLeftSeq[i] < [n][j]
				{
					assert [n][j] == n;
					assert newLeftSeq[i] in NumbersInTree(newLeft);
					assert newLeftSeq[i] in NumbersInTree(left) + {x};
					if newLeftSeq[i] == x {
						assert x < n;
					} else {
						assert newLeftSeq[i] in NumbersInTree(left);
						assert newLeftSeq[i] < n;
					}
				}
				
				forall i, j | 0 <= i < 1 && 0 <= j < |rightSeq|
					ensures [n][i] < rightSeq[j]
				{
					assert [n][i] == n;
					assert rightSeq[j] in NumbersInTree(right);
					assert n < rightSeq[j];
				}
				
				ProveNewSequenceAscending(newSeq, newLeftSeq, [n], rightSeq);
			} else {
				var newRight :| BST(newRight) && NumbersInTree(newRight) == NumbersInTree(right) + {x} && t == Node(n, left, newRight);
				BSTOrderingProperties(newRight);
				
				var leftSeq := Inorder(left);
				var newRightSeq := Inorder(newRight);
				var newSeq := leftSeq + [n] + newRightSeq;
				
				assert Inorder(t) == newSeq;
				assert NumbersInTree(t) == NumbersInTree(t0) + {x};
				
				// Establish that the new sequence is ascending
				assert BST(left);
				assert Ascending(leftSeq);
				assert BST(newRight);
				assert Ascending(newRightSeq);
				
				// Prove ordering between parts
				forall i, j | 0 <= i < |leftSeq| && 0 <= j < 1
					ensures leftSeq[i] < [n][j]
				{
					assert [n][j] == n;
					assert leftSeq[i] in NumbersInTree(left);
					assert leftSeq[i] < n;
				}
				
				forall i, j | 0 <= i < 1 && 0 <= j < |newRightSeq|
					ensures [n][i] < newRightSeq[j]
				{
					assert [n][i] == n;
					assert newRightSeq[j] in NumbersInTree(newRight);
					assert newRightSeq[j] in NumbersInTree(right) + {x};
					if newRightSeq[j] == x {
						assert n < x;
					} else {
						assert newRightSeq[j] in NumbersInTree(right);
						assert n < newRightSeq[j];
					}
				}
				
				ProveNewSequenceAscending(newSeq, leftSeq, [n], newRightSeq);
			}
	}
}

//IMPL
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{
	match t0 {
		case Empty => 
			t := Node(x, Empty, Empty);
		case Node(n, left, right) =>
			/* code modified by LLM (iteration 4): Added lemma calls to establish preconditions */
			SubtreesOfBSTAreBST(t0);
			ElementNotInSubtrees(t0, x);
			
			if x < n {
				var newLeft := InsertBST(left, x);
				t := Node(n, newLeft, right);
			} else {
				var newRight := InsertBST(right, x);
				t := Node(n, left, newRight);
			}
			
			/* code modified by LLM (iteration 4): Added lemma call to prove postcondition */
			InsertPreservesBST(t0, x, t);
	}
}
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

/* code modified by LLM (iteration 1): Added helper lemma for sequence concatenation and numbers in sequence */
lemma NumbersInSequenceConcatenation(s1: seq<int>, s2: seq<int>)
	ensures NumbersInSequence(s1 + s2) == NumbersInSequence(s1) + NumbersInSequence(s2)
{
	// Proof by set comprehension properties
}

/* code modified by LLM (iteration 1): Added helper lemma for single element sequence */
lemma NumbersInSingleElement(x: int)
	ensures NumbersInSequence([x]) == {x}
{
}

/* code modified by LLM (iteration 1): Added helper lemma for tree numbers decomposition */
lemma NumbersInTreeDecomposition(t1: Tree, t2: Tree, n: int)
	ensures NumbersInTree(Node(n, t1, t2)) == NumbersInTree(t1) + {n} + NumbersInTree(t2)
{
	calc {
		NumbersInTree(Node(n, t1, t2));
		NumbersInSequence(Inorder(Node(n, t1, t2)));
		NumbersInSequence(Inorder(t1) + [n] + Inorder(t2));
		{ NumbersInSequenceConcatenation(Inorder(t1) + [n], Inorder(t2)); }
		NumbersInSequence(Inorder(t1) + [n]) + NumbersInSequence(Inorder(t2));
		{ NumbersInSequenceConcatenation(Inorder(t1), [n]); }
		NumbersInSequence(Inorder(t1)) + NumbersInSequence([n]) + NumbersInSequence(Inorder(t2));
		{ NumbersInSingleElement(n); }
		NumbersInSequence(Inorder(t1)) + {n} + NumbersInSequence(Inorder(t2));
		NumbersInTree(t1) + {n} + NumbersInTree(t2);
	}
}

/* code modified by LLM (iteration 1): Added lemma for proving ascending property of concatenated sequences */
lemma AscendingConcatenation(s1: seq<int>, s2: seq<int>, x: int)
	requires Ascending(s1) && Ascending(s2)
	requires forall i :: 0 <= i < |s1| ==> s1[i] < x
	requires forall i :: 0 <= i < |s2| ==> x < s2[i]
	ensures Ascending(s1 + [x] + s2)
{
	var result := s1 + [x] + s2;
	forall i, j | 0 <= i < j < |result|
		ensures result[i] < result[j]
	{
		if j < |s1| {
			// Both in s1
			assert result[i] == s1[i] && result[j] == s1[j];
		} else if i < |s1| && j == |s1| {
			// i in s1, j is x
			assert result[i] == s1[i] && result[j] == x;
		} else if i < |s1| && j > |s1| {
			// i in s1, j in s2
			assert result[i] == s1[i] && result[j] == s2[j - |s1| - 1];
		} else if i == |s1| && j > |s1| {
			// i is x, j in s2
			assert result[i] == x && result[j] == s2[j - |s1| - 1];
		} else {
			// Both in s2
			assert result[i] == s2[i - |s1| - 1] && result[j] == s2[j - |s1| - 1];
		}
	}
}

/* code modified by LLM (iteration 1): Added lemma for BST ordering properties */
lemma BSTOrdering(t: Tree, x: int)
	requires BST(t)
	ensures forall y :: y in NumbersInTree(t) ==> 
		(match t 
		case Empty => true
		case Node(n, _, _) => y in NumbersInTree(t))
{
}

/* code modified by LLM (iteration 1): Added lemma for left subtree ordering */
lemma LeftSubtreeOrdering(t1: Tree, t2: Tree, n: int, x: int)
	requires BST(Node(n, t1, t2))
	requires x < n
	ensures forall y :: y in NumbersInTree(t1) ==> y < n
	ensures forall y :: y in NumbersInTree(t2) ==> n < y
{
	var inorder := Inorder(Node(n, t1, t2));
	var left_inorder := Inorder(t1);
	var right_inorder := Inorder(t2);
	
	assert inorder == left_inorder + [n] + right_inorder;
	assert Ascending(inorder);
	
	// Prove left subtree elements < n
	forall y | y in NumbersInTree(t1)
		ensures y < n
	{
		// y appears in left_inorder, which appears before n in inorder
		assert y in NumbersInSequence(left_inorder);
		// Since inorder is ascending and y appears before n, we have y < n
	}
	
	// Prove right subtree elements > n  
	forall y | y in NumbersInTree(t2)
		ensures n < y
	{
		// y appears in right_inorder, which appears after n in inorder
		assert y in NumbersInSequence(right_inorder);
		// Since inorder is ascending and y appears after n, we have n < y
	}
}

//IMPL InsertBST
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{
	match t0 {
		case Empty => 
			t := Node(x, Empty, Empty);
			/* code modified by LLM (iteration 1): Added proof for empty case */
			assert Inorder(t) == [x];
			assert Ascending([x]);
		case Node(n', nt1, nt2) =>
			/* code modified by LLM (iteration 1): Added proof context for node case */
			NumbersInTreeDecomposition(nt1, nt2, n');
			assert x != n';
			LeftSubtreeOrdering(nt1, nt2, n', x);
			
			if x < n' {
				/* code modified by LLM (iteration 1): Added assertion for left subtree property */
				assert x !in NumbersInTree(nt1);
				var newLeft := InsertBST(nt1, x);
				t := Node(n', newLeft, nt2);
				
				/* code modified by LLM (iteration 1): Enhanced proof for left insertion case */
				NumbersInTreeDecomposition(newLeft, nt2, n');
				assert NumbersInTree(t) == NumbersInTree(newLeft) + {n'} + NumbersInTree(nt2);
				assert NumbersInTree(newLeft) == NumbersInTree(nt1) + {x};
				assert NumbersInTree(t) == NumbersInTree(t0) + {x};
				
				// Prove BST property
				assert BST(newLeft);
				assert BST(nt2);
				
				// Show ordering properties hold
				assert forall y :: y in NumbersInTree(newLeft) ==> y < n';
				assert forall y :: y in NumbersInTree(nt2) ==> n' < y;
				
				// Apply ascending concatenation lemma
				AscendingConcatenation(Inorder(newLeft), Inorder(nt2), n');
				assert Ascending(Inorder(newLeft) + [n'] + Inorder(nt2));
				assert Ascending(Inorder(t));
				assert BST(t);
				
			} else {
				/* code modified by LLM (iteration 1): Added assertion for right subtree property */
				assert x !in NumbersInTree(nt2);
				var newRight := InsertBST(nt2, x);  
				t := Node(n', nt1, newRight);
				
				/* code modified by LLM (iteration 1): Enhanced proof for right insertion case */
				NumbersInTreeDecomposition(nt1, newRight, n');
				assert NumbersInTree(t) == NumbersInTree(nt1) + {n'} + NumbersInTree(newRight);
				assert NumbersInTree(newRight) == NumbersInTree(nt2) + {x};
				assert NumbersInTree(t) == NumbersInTree(t0) + {x};
				
				// Prove BST property
				assert BST(nt1);
				assert BST(newRight);
				
				// Show ordering properties hold
				assert forall y :: y in NumbersInTree(nt1) ==> y < n';
				assert forall y :: y in NumbersInTree(newRight) ==> n' < y;
				
				// Apply ascending concatenation lemma
				AscendingConcatenation(Inorder(nt1), Inorder(newRight), n');
				assert Ascending(Inorder(nt1) + [n'] + Inorder(newRight));
				assert Ascending(Inorder(t));
				assert BST(t);
			}
	}
}
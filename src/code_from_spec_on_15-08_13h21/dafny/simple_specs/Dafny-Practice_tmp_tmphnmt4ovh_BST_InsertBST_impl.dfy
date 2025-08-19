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

/* code modified by LLM (iteration 2): Added lemma to prove subsequence ordering properties */
lemma SubsequenceAscending(s: seq<int>, i: int, j: int)
	requires Ascending(s)
	requires 0 <= i <= j <= |s|
	ensures Ascending(s[i..j])
{
	forall a, b | 0 <= a < b < |s[i..j]|
		ensures s[i..j][a] < s[i..j][b]
	{
		assert s[i..j][a] == s[i + a];
		assert s[i..j][b] == s[i + b];
		assert 0 <= i + a < i + b < |s|;
	}
}

/* code modified by LLM (iteration 2): Fixed helper lemma to properly prove subtree BST properties */
lemma SubtreeBST(t: Tree)
	requires BST(t)
	ensures match t {
		case Empty => true
		case Node(val, left, right) => BST(left) && BST(right)
	}
{
	match t {
		case Empty => 
		case Node(val, left, right) => 
			var leftInorder := Inorder(left);
			var rightInorder := Inorder(right);
			var fullInorder := Inorder(t);
			
			assert fullInorder == leftInorder + [val] + rightInorder;
			assert Ascending(fullInorder);
			
			/* code modified by LLM (iteration 2): Use subsequence lemma to prove left subtree ordering */
			SubsequenceAscending(fullInorder, 0, |leftInorder|);
			assert leftInorder == fullInorder[0..|leftInorder|];
			assert Ascending(leftInorder);
			assert BST(left);
			
			/* code modified by LLM (iteration 2): Use subsequence lemma to prove right subtree ordering */
			SubsequenceAscending(fullInorder, |leftInorder| + 1, |fullInorder|);
			assert rightInorder == fullInorder[|leftInorder| + 1..|fullInorder|];
			assert Ascending(rightInorder);
			assert BST(right);
	}
}

/* code modified by LLM (iteration 2): Simplified and fixed lemma with correct preconditions */
lemma InsertPreservesBST(t0: Tree, x: int, newSubtree: Tree, val: int, otherSubtree: Tree, isLeftInsertion: bool)
	requires BST(t0)
	requires x !in NumbersInTree(t0)
	requires match t0 { case Node(v, l, r) => val == v && (if isLeftInsertion then otherSubtree == r else otherSubtree == l) case Empty => false }
	requires BST(newSubtree)
	requires if isLeftInsertion then 
		(NumbersInTree(newSubtree) == (match t0 { case Node(v, l, r) => NumbersInTree(l) case Empty => {} }) + {x} && x < val)
	else 
		(NumbersInTree(newSubtree) == (match t0 { case Node(v, l, r) => NumbersInTree(r) case Empty => {} }) + {x} && x > val)
	ensures BST(if isLeftInsertion then Node(val, newSubtree, otherSubtree) else Node(val, otherSubtree, newSubtree))
	ensures NumbersInTree(if isLeftInsertion then Node(val, newSubtree, otherSubtree) else Node(val, otherSubtree, newSubtree)) == NumbersInTree(t0) + {x}
{
	var result := if isLeftInsertion then Node(val, newSubtree, otherSubtree) else Node(val, otherSubtree, newSubtree);
	
	/* code modified by LLM (iteration 2): Prove the result is BST by showing inorder traversal is ascending */
	if isLeftInsertion {
		var newLeftInorder := Inorder(newSubtree);
		var rightInorder := Inorder(otherSubtree);
		var resultInorder := newLeftInorder + [val] + rightInorder;
		
		assert Inorder(result) == resultInorder;
		assert BST(newSubtree) && BST(otherSubtree);
		
		// Prove ascending property
		forall i, j | 0 <= i < j < |resultInorder|
			ensures resultInorder[i] < resultInorder[j]
		{
			if j < |newLeftInorder| {
				// Both in left subtree
				assert resultInorder[i] < resultInorder[j];
			} else if i < |newLeftInorder| && j == |newLeftInorder| {
				// i in left, j is val
				assert resultInorder[i] < val;
			} else if i < |newLeftInorder| && j > |newLeftInorder| {
				// i in left, j in right
				assert resultInorder[i] < val < resultInorder[j];
			} else if i == |newLeftInorder| && j > |newLeftInorder| {
				// i is val, j in right
				assert val < resultInorder[j];
			} else {
				// Both in right subtree
				assert resultInorder[i] < resultInorder[j];
			}
		}
		assert Ascending(resultInorder);
	} else {
		var leftInorder := Inorder(otherSubtree);
		var newRightInorder := Inorder(newSubtree);
		var resultInorder := leftInorder + [val] + newRightInorder;
		
		assert Inorder(result) == resultInorder;
		assert BST(otherSubtree) && BST(newSubtree);
		
		// Prove ascending property
		forall i, j | 0 <= i < j < |resultInorder|
			ensures resultInorder[i] < resultInorder[j]
		{
			if j < |leftInorder| {
				// Both in left subtree
				assert resultInorder[i] < resultInorder[j];
			} else if i < |leftInorder| && j == |leftInorder| {
				// i in left, j is val
				assert resultInorder[i] < val;
			} else if i < |leftInorder| && j > |leftInorder| {
				// i in left, j in right
				assert resultInorder[i] < val < resultInorder[j];
			} else if i == |leftInorder| && j > |leftInorder| {
				// i is val, j in right
				assert val < resultInorder[j];
			} else {
				// Both in right subtree
				assert resultInorder[i] < resultInorder[j];
			}
		}
		assert Ascending(resultInorder);
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
		case Node(val, left, right) =>
			/* code modified by LLM (iteration 2): Added lemma call to establish subtree BST properties */
			SubtreeBST(t0);
			
			if x < val {
				var newLeft := InsertBST(left, x);
				t := Node(val, newLeft, right);
				
				/* code modified by LLM (iteration 2): Added lemma call with correct parameters */
				InsertPreservesBST(t0, x, newLeft, val, right, true);
			} else {
				var newRight := InsertBST(right, x);
				t := Node(val, left, newRight);
				
				/* code modified by LLM (iteration 2): Added lemma call with correct parameters */
				InsertPreservesBST(t0, x, newRight, val, left, false);
			}
	}
}
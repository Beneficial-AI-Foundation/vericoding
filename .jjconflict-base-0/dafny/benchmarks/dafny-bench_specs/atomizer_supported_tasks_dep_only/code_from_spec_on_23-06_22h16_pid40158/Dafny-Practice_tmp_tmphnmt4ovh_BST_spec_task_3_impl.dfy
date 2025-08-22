// ATOM Tree
datatype Tree = Empty | Node(data: int, left: Tree, right: Tree)

// ATOM Main
method Main() {
    var q := [1, 3, 2, 5, 4];
    var t := BuildBST(q);
    PrintTreeNumbersInorder(t);
}

// ATOM PrintTreeNumbersInorder
method PrintTreeNumbersInorder(t: Tree) {
    var inorder_seq := Inorder(t);
    print "Inorder traversal: ";
    var i := 0;
    while i < |inorder_seq| {
        print inorder_seq[i];
        if i < |inorder_seq| - 1 {
            print ", ";
        }
        i := i + 1;
    }
    print "\n";
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

// IMPL BuildBST
method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
    t := Empty;
    var i := 0;
    while i < |q|
        invariant 0 <= i <= |q|
        invariant BST(t)
        invariant NumbersInTree(t) == NumbersInSequence(q[..i])
    {
        /* code modified by LLM (iteration 2): Simplified assertion to establish precondition for InsertBST */
        assert q[i] !in NumbersInTree(t) by {
            assert NumbersInTree(t) == NumbersInSequence(q[..i]);
            assert q[i] !in q[..i];
        }
        t := InsertBST(t, q[i]);
        /* code modified by LLM (iteration 2): Simplified assertion to maintain loop invariant */
        assert NumbersInTree(t) == NumbersInSequence(q[..i+1]) by {
            assert q[..i+1] == q[..i] + [q[i]];
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 2): Added final assertion to establish postcondition */
    assert q[..|q|] == q;
}

// IMPL InsertBST
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0) + {x}
{
	match t0 
	{
		case Empty => 
        {
            t := Node(x, Empty, Empty);
        }

		case Node(i, left, right) => 
		{
			if x < i
			{
				/* code modified by LLM (iteration 2): Use lemma to establish BST properties of subtrees */
				LemmaBinarySearchSubtree(i, left, right);
				var tmp := InsertBST(left, x);
				t := Node(i, tmp, right);
				
                /* code modified by LLM (iteration 2): Use helper lemma to prove BST property */
                LemmaInsertBSTLeft(i, left, right, x, tmp);
			}
			else
			{
				/* code modified by LLM (iteration 2): Use lemma to establish BST properties of subtrees */
				LemmaBinarySearchSubtree(i, left, right);
				var tmp := InsertBST(right, x);
				t := Node(i, left, tmp);

                /* code modified by LLM (iteration 2): Use helper lemma to prove BST property */
                LemmaInsertBSTRight(i, left, right, x, tmp);
			}
		}
	}
}

/* code modified by LLM (iteration 2): Added helper lemma for left insertion */
lemma LemmaInsertBSTLeft(i: int, left: Tree, right: Tree, x: int, tmp: Tree)
    requires BST(Node(i, left, right))
    requires x < i
    requires x !in NumbersInTree(left)
    requires BST(tmp) && NumbersInTree(tmp) == NumbersInTree(left) + {x}
    ensures BST(Node(i, tmp, right))
    ensures NumbersInTree(Node(i, tmp, right)) == NumbersInTree(Node(i, left, right)) + {x}
{
    LemmaBinarySearchSubtree(i, left, right);
    var left_seq := Inorder(left);
    var tmp_seq := Inorder(tmp);
    var right_seq := Inorder(right);
    var result_seq := tmp_seq + [i] + right_seq;
    
    assert forall y :: y in tmp_seq ==> y < i by {
        assert forall y :: y in NumbersInTree(tmp) ==> y < i by {
            assert NumbersInTree(tmp) == NumbersInTree(left) + {x};
            assert forall z :: z in NumbersInTree(left) ==> z < i;
            assert x < i;
        }
        lemma_all_small(tmp_seq, i);
    }
    
    assert forall y :: y in right_seq ==> y > i by {
        lemma_all_big(right_seq, i);
    }
    
    LemmaAscendingConcatenation(tmp_seq, [i], right_seq);
}

/* code modified by LLM (iteration 2): Added helper lemma for right insertion */
lemma LemmaInsertBSTRight(i: int, left: Tree, right: Tree, x: int, tmp: Tree)
    requires BST(Node(i, left, right))
    requires x > i
    requires x !in NumbersInTree(right)
    requires BST(tmp) && NumbersInTree(tmp) == NumbersInTree(right) + {x}
    ensures BST(Node(i, left, tmp))
    ensures NumbersInTree(Node(i, left, tmp)) == NumbersInTree(Node(i, left, right)) + {x}
{
    LemmaBinarySearchSubtree(i, left, right);
    var left_seq := Inorder(left);
    var tmp_seq := Inorder(tmp);
    var right_seq := Inorder(right);
    var result_seq := left_seq + [i] + tmp_seq;
    
    assert forall y :: y in left_seq ==> y < i by {
        lemma_all_small(left_seq, i);
    }
    
    assert forall y :: y in tmp_seq ==> y > i by {
        assert forall y :: y in NumbersInTree(tmp) ==> y > i by {
            assert NumbersInTree(tmp) == NumbersInTree(right) + {x};
            assert forall z :: z in NumbersInTree(right) ==> z > i;
            assert x > i;
        }
        lemma_all_big(tmp_seq, i);
    }
    
    LemmaAscendingConcatenation(left_seq, [i], tmp_seq);
}

/* code modified by LLM (iteration 2): Added helper lemma for concatenation */
lemma LemmaAscendingConcatenation(s1: seq<int>, s2: seq<int>, s3: seq<int>)
    requires Ascending(s1)
    requires Ascending(s2)
    requires Ascending(s3)
    requires forall x, y :: x in s1 && y in s2 ==> x < y
    requires forall x, y :: x in s2 && y in s3 ==> x < y
    ensures Ascending(s1 + s2 + s3)
{
}

// ATOM LemmaBinarySearchSubtree
lemma LemmaBinarySearchSubtree(i: int, left: Tree, right: Tree)
    requires BST(Node(i, left, right))
    ensures BST(left) && BST(right)
    ensures forall x :: x in NumbersInTree(left) ==> x < i
    ensures forall x :: x in NumbersInTree(right) ==> x > i
{
    var inorder_seq := Inorder(Node(i, left, right));
    var left_seq := Inorder(left);
    var right_seq := Inorder(right);
    
    LemmaAscendingSubsequence(inorder_seq, 0, |left_seq|);
    LemmaAscendingSubsequence(inorder_seq, |left_seq| + 1, |inorder_seq|);
}

// ATOM LemmaAscendingSubsequence
lemma LemmaAscendingSubsequence(q: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |q|
    requires Ascending(q)
    ensures Ascending(q[start..end])
{
}

// ATOM lemma_all_small
lemma lemma_all_small(q: seq<int>, i: int)
	requires forall k :: k in NumbersInSequence(q) ==> k < i
	requires forall k :: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
	ensures forall j :: 0 <= j < |q| ==> q[j] < i
{
}

// ATOM lemma_all_big
lemma lemma_all_big(q: seq<int>, i: int)
	requires forall k :: k in NumbersInSequence(q) ==> k > i
	requires forall k :: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
	ensures forall j :: 0 <= j < |q| ==> q[j] > i
{
}
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
  assume {:axiom} BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x};
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


//IMPL
method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
    /* code modified by LLM (iteration 3): Handle empty sequence */
    if |q| == 0 {
        t := Empty;
        return;
    }
    
    /* code modified by LLM (iteration 3): Sort the sequence first to ensure BST property */
    var sorted_q := SortSequence(q);
    
    /* code modified by LLM (iteration 3): Build BST from sorted sequence */
    t := BuildBSTFromSorted(sorted_q);
    
    /* code modified by LLM (iteration 3): Assert properties are maintained */
    assert NumbersInSequence(sorted_q) == NumbersInSequence(q);
    assert BST(t);
    assert NumbersInTree(t) == NumbersInSequence(sorted_q);
}

/* code modified by LLM (iteration 3): Helper method to sort sequence */
method SortSequence(q: seq<int>) returns (sorted: seq<int>)
    requires NoDuplicates(q)
    ensures NoDuplicates(sorted)
    ensures Ascending(sorted)
    ensures NumbersInSequence(sorted) == NumbersInSequence(q)
    ensures |sorted| == |q|
{
    sorted := q;
    var i := 0;
    while i < |sorted|
        invariant 0 <= i <= |sorted|
        invariant NumbersInSequence(sorted) == NumbersInSequence(q)
        invariant NoDuplicates(sorted)
        invariant |sorted| == |q|
        invariant forall x, y :: 0 <= x < y < i ==> sorted[x] < sorted[y]
    {
        var j := i;
        while j > 0 && sorted[j-1] > sorted[j]
            invariant 0 <= j <= i
            invariant NumbersInSequence(sorted) == NumbersInSequence(q)
            invariant NoDuplicates(sorted)
            invariant |sorted| == |q|
        {
            sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
            j := j - 1;
        }
        i := i + 1;
    }
}

/* code modified by LLM (iteration 3): Helper method to build BST from sorted sequence */
method BuildBSTFromSorted(q: seq<int>) returns (t: Tree)
    requires NoDuplicates(q)
    requires Ascending(q)
    ensures BST(t)
    ensures NumbersInTree(t) == NumbersInSequence(q)
    decreases |q|
{
    if |q| == 0 {
        t := Empty;
        return;
    }
    
    if |q| == 1 {
        t := Node(q[0], Empty, Empty);
        return;
    }
    
    /* code modified by LLM (iteration 3): Use middle element for balanced BST */
    var mid := |q| / 2;
    var left_seq := q[..mid];
    var right_seq := q[mid+1..];
    
    /* code modified by LLM (iteration 3): Recursively build subtrees */
    var left := BuildBSTFromSorted(left_seq);
    var right := BuildBSTFromSorted(right_seq);
    
    t := Node(q[mid], left, right);
    
    /* code modified by LLM (iteration 3): Assert BST property is maintained */
    assert Ascending(left_seq);
    assert Ascending(right_seq);
    assert BST(left);
    assert BST(right);
    assert forall x :: x in NumbersInTree(left) ==> x < q[mid];
    assert forall x :: x in NumbersInTree(right) ==> x > q[mid];
}

/*
	Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/
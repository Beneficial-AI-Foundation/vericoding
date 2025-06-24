// ATOM Tree
datatype Tree = Empty | Node(data: int, left: Tree, right: Tree)

// IMPL Main
method Main() {
}

// IMPL PrintTreeNumbersInorder
method PrintTreeNumbersInorder(t: Tree)
{
    var inorder_seq := Inorder(t);
    var i := 0;
    while i < |inorder_seq|
        /* code modified by LLM (iteration 4): added loop invariant for bounds checking */
        invariant 0 <= i <= |inorder_seq|
    {
        print inorder_seq[i];
        print " ";
        i := i + 1;
    }
}

// ATOM NumbersInTree
function NumbersInTree(t: Tree): set<int>
{
    NumbersInSequence(Inorder(t))
}

// ATOM NumbersInSequence
function NumbersInSequence(q: seq<int>): set<int>
{
    set x | x in q
}

// ATOM BST
predicate BST(t: Tree)
{
    Ascending(Inorder(t))
}

// ATOM Inorder
function Inorder(t: Tree): seq<int>
{
    match t {
        case Empty => []
        case Node(n', nt1, nt2) => Inorder(nt1) + [n'] + Inorder(nt2)
    }
}

// ATOM Ascending
predicate Ascending(q: seq<int>)
{
    forall i, j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

// ATOM NoDuplicates
predicate NoDuplicates(q: seq<int>) { 
    forall i, j :: 0 <= i < j < |q| ==> q[i] != q[j] 
}

/* code modified by LLM (iteration 4): added helper lemma for sequence slicing */
lemma LemmaSequenceSliceEquality(q: seq<int>, i: int)
    requires 0 <= i < |q|
    ensures NumbersInSequence(q[0..i+1]) == NumbersInSequence(q[0..i]) + {q[i]}
{
    var left := q[0..i];
    var full := q[0..i+1];
    assert full == left + [q[i]];
    
    forall x | x in NumbersInSequence(full)
        ensures x in NumbersInSequence(left) + {q[i]}
    {
        if x == q[i] {
            assert x in {q[i]};
        } else {
            assert x in NumbersInSequence(left);
        }
    }
    
    forall x | x in NumbersInSequence(left) + {q[i]}
        ensures x in NumbersInSequence(full)
    {
        if x in NumbersInSequence(left) {
            assert x in full;
        } else {
            assert x == q[i];
            assert x in full;
        }
    }
}

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
        invariant NumbersInTree(t) == NumbersInSequence(q[0..i])
    {
        /* code modified by LLM (iteration 4): added assertion using NoDuplicates precondition to prove q[i] not in tree */
        assert forall j :: 0 <= j < i ==> q[j] != q[i];
        assert q[i] !in NumbersInSequence(q[0..i]);
        assert NumbersInTree(t) == NumbersInSequence(q[0..i]);
        assert q[i] !in NumbersInTree(t);
        
        t := InsertBST(t, q[i]);
        i := i + 1;
        
        /* code modified by LLM (iteration 4): added lemma call and assertion to help prove loop invariant maintenance */
        LemmaSequenceSliceEquality(q, i-1);
        assert NumbersInSequence(q[0..i]) == NumbersInSequence(q[0..i-1]) + {q[i-1]};
    }
}

// IMPL InsertBST
method InsertBST(t0: Tree, x: int) returns (t: Tree)
    requires BST(t0) && x !in NumbersInTree(t0)
    ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0) + {x}
{
    match t0 
    {
        case Empty => 
            t := Node(x, Empty, Empty);
            /* code modified by LLM (iteration 4): added assertions to verify postconditions for Empty case */
            assert NumbersInTree(t) == {x};
            assert NumbersInTree(t0) == {};
            assert BST(t);

        case Node(i, left, right) => 
        {
            if x < i
            {
                LemmaBinarySearchSubtree(i, left, right);
                /* code modified by LLM (iteration 4): added assertion to verify precondition for recursive call */
                assert x !in NumbersInTree(left);
                var new_left := InsertBST(left, x);
                t := Node(i, new_left, right);
                
                ghost var left_nums := Inorder(left);
                ghost var right_nums := Inorder(right);
                ghost var new_left_nums := Inorder(new_left);
                
                /* code modified by LLM (iteration 4): added assertions to help verify BST property */
                assert NumbersInTree(new_left) == NumbersInTree(left) + {x};
                assert forall y :: y in NumbersInTree(new_left) ==> y < i;
                assert forall y :: y in NumbersInTree(right) ==> y > i;
                
                lemma_all_small(new_left_nums, i);
                LemmaAscendingConcatenation(new_left_nums, [i], right_nums);
                
                /* code modified by LLM (iteration 4): added final assertions */
                assert BST(t);
                assert NumbersInTree(t) == NumbersInTree(t0) + {x};
            }
            else
            {
                LemmaBinarySearchSubtree(i, left, right);
                /* code modified by LLM (iteration 4): added assertion to verify precondition for recursive call */
                assert x !in NumbersInTree(right);
                var new_right := InsertBST(right, x);
                t := Node(i, left, new_right);
                
                ghost var left_nums := Inorder(left);
                ghost var right_nums := Inorder(right);
                ghost var new_right_nums := Inorder(new_right);
                
                /* code modified by LLM (iteration 4): added assertions to help verify BST property */
                assert NumbersInTree(new_right) == NumbersInTree(right) + {x};
                assert forall y :: y in NumbersInTree(left) ==> y < i;
                assert forall y :: y in NumbersInTree(new_right) ==> y > i;
                
                lemma_all_big(new_right_nums, i);
                LemmaAscendingConcatenation(left_nums, [i], new_right_nums);
                
                /* code modified by LLM (iteration 4): added final assertions */
                assert BST(t);
                assert NumbersInTree(t) == NumbersInTree(t0) + {x};
            }
        }
    }
}

// ATOM LemmaBinarySearchSubtree
lemma LemmaBinarySearchSubtree(i: int, left: Tree, right: Tree)
    requires BST(Node(i, left, right))
    ensures BST(left)
    ensures BST(right)
    ensures forall x :: x in NumbersInTree(left) ==> x < i
    ensures forall x :: x in NumbersInTree(right) ==> x > i
{
    var left_seq := Inorder(left);
    var right_seq := Inorder(right);
    var full_seq := left_seq + [i] + right_seq;
    
    LemmaAscendingSubsequence(full_seq, 0, |left_seq|);
    LemmaAscendingSubsequence(full_seq, |left_seq| + 1, |full_seq|);
}

// ATOM LemmaAscendingSubsequence
lemma LemmaAscendingSubsequence(q: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |q|
    requires Ascending(q)
    ensures Ascending(q[start..end])
{
}

// ATOM LemmaAscendingConcatenation
lemma LemmaAscendingConcatenation(left: seq<int>, middle: seq<int>, right: seq<int>)
    requires Ascending(left)
    requires Ascending(middle) 
    requires Ascending(right)
    requires forall i, j :: i in left && j in middle ==> i < j
    requires forall i, j :: i in middle && j in right ==> i < j
    ensures Ascending(left + middle + right)
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
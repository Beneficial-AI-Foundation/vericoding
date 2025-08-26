datatype Tree = Empty | Node(int, Tree, Tree)

function NumbersInTree(t: Tree): set<int>
{
    NumbersInSequence(Inorder(t))
}

function NumbersInSequence(q: seq<int>): set<int>
{
    set x | x in q
}

predicate BST(t: Tree)
{
    Ascending(Inorder(t))
}

function Inorder(t: Tree): seq<int>
{
    match t {
        case Empty => []
        case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
    }
}

predicate Ascending(q: seq<int>)
{
    forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

/*
    Goal: Implement correctly, clearly. No need to document the proof obligations.
*/

/*
    Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
    as we've learned, with assertions and a lemma for each proof goal
*/

// <vc-helpers>
lemma LemmaBSTSubtreeProperty(n: int, left: Tree, right: Tree)
    requires BST(Node(n, left, right))
    ensures BST(left) && BST(right)
    ensures forall k :: k in NumbersInTree(left) ==> k < n
    ensures forall k :: k in NumbersInTree(right) ==> k > n
{
    LemmaBinarySearchSubtree(n, left, right);
    var qleft := Inorder(left);
    var qright := Inorder(right);
    var q := qleft + [n] + qright;
    
    // Prove all elements in left subtree are < n
    if |qleft| > 0 {
        assert forall j :: 0 <= j < |qleft| ==> q[j] < q[|qleft|];
        assert q[|qleft|] == n;
        assert forall j :: 0 <= j < |qleft| ==> qleft[j] < n;
        assert forall k :: 0 <= k < |qleft| ==> qleft[k] in NumbersInSequence(qleft);
        lemma_all_small(qleft, n);
    }
    
    // Prove all elements in right subtree are > n
    if |qright| > 0 {
        assert forall j :: |qleft| + 1 <= j < |q| ==> q[|qleft|] < q[j];
        assert q[|qleft|] == n;
        assert forall j :: 0 <= j < |qright| ==> n < qright[j];
        assert forall k :: 0 <= k < |qright| ==> qright[k] in NumbersInSequence(qright);
        lemma_all_big(qright, n);
    }
}

function InsertBSTHelper(t0: Tree, x: int): Tree
    requires BST(t0) && x !in NumbersInTree(t0)
    ensures BST(InsertBSTHelper(t0, x)) && NumbersInTree(InsertBSTHelper(t0, x)) == NumbersInTree(t0) + {x}
{
    match t0 {
        case Empty => 
            LemmaNumbersInSequenceSingle(x);
            Node(x, Empty, Empty)
        case Node(n, left, right) => 
            LemmaBSTSubtreeProperty(n, left, right);
            if x < n then 
                var newLeft := InsertBSTHelper(left, x);
                assert BST(newLeft);
                assert NumbersInTree(newLeft) == NumbersInTree(left) + {x};
                
                var result := Node(n, newLeft, right);
                LemmaInsertLeftPreservesBST(n, left, right, x, newLeft);
                result
            else 
                var newRight := InsertBSTHelper(right, x);
                assert BST(newRight);
                assert NumbersInTree(newRight) == NumbersInTree(right) + {x};
                
                var result := Node(n, left, newRight);
                LemmaInsertRightPreservesBST(n, left, right, x, newRight);
                result
    }
}

lemma LemmaInsertLeftPreservesBST(n: int, left: Tree, right: Tree, x: int, newLeft: Tree)
    requires BST(Node(n, left, right))
    requires x < n
    requires x !in NumbersInTree(Node(n, left, right))
    requires BST(left)
    requires x !in NumbersInTree(left)
    requires newLeft == InsertBSTHelper(left, x)
    requires BST(newLeft)
    requires NumbersInTree(newLeft) == NumbersInTree(left) + {x}
    ensures BST(Node(n, newLeft, right))
    ensures NumbersInTree(Node(n, newLeft, right)) == NumbersInTree(Node(n, left, right)) + {x}
{
    var qleft := Inorder(left);
    var qright := Inorder(right);
    var qnewLeft := Inorder(newLeft);
    var oldSeq := qleft + [n] + qright;
    var newSeq := qnewLeft + [n] + qright;
    
    assert Ascending(oldSeq);
    assert Ascending(qnewLeft);
    
    // Prove that all elements in newLeft are still < n
    LemmaBSTSubtreeProperty(n, left, right);
    assert forall k :: k in NumbersInTree(left) ==> k < n;
    assert x < n;
    assert NumbersInTree(newLeft) == NumbersInTree(left) + {x};
    assert forall k :: k in NumbersInTree(newLeft) ==> k < n;
    
    // Prove that all elements in right are still > n  
    assert forall k :: k in NumbersInTree(right) ==> k > n;
    
    // Prove ascending property of the new sequence
    LemmaAscendingConcatenation(qnewLeft, [n], qright, n);
    
    LemmaNumbersInSequenceConcatenation(qnewLeft, [n], qright);
    LemmaNumbersInSequenceConcatenation(qleft, [n], qright);
    LemmaNumbersInSequenceSingle(n);
}

lemma LemmaInsertRightPreservesBST(n: int, left: Tree, right: Tree, x: int, newRight: Tree)
    requires BST(Node(n, left, right))
    requires x > n
    requires x !in NumbersInTree(Node(n, left, right))
    requires BST(right)
    requires x !in NumbersInTree(right)
    requires newRight == InsertBSTHelper(right, x)
    requires BST(newRight)
    requires NumbersInTree(newRight) == NumbersInTree(right) + {x}
    ensures BST(Node(n, left, newRight))
    ensures NumbersInTree(Node(n, left, newRight)) == NumbersInTree(Node(n, left, right)) + {x}
{
    var qleft := Inorder(left);
    var qright := Inorder(right);
    var qnewRight := Inorder(newRight);
    var oldSeq := qleft + [n] + qright;
    var newSeq := qleft + [n] + qnewRight;
    
    assert Ascending(oldSeq);
    assert Ascending(qnewRight);
    
    // Prove that all elements in left are still < n
    LemmaBSTSubtreeProperty(n, left, right);
    assert forall k :: k in NumbersInTree(left) ==> k < n;
    
    // Prove that all elements in newRight are > n
    assert forall k :: k in NumbersInTree(right) ==> k > n;
    assert x > n;
    assert NumbersInTree(newRight) == NumbersInTree(right) + {x};
    assert forall k :: k in NumbersInTree(newRight) ==> k > n;
    
    // Prove ascending property of the new sequence
    LemmaAscendingConcatenation(qleft, [n], qnewRight, n);
    
    LemmaNumbersInSequenceConcatenation(qleft, [n], qnewRight);
    LemmaNumbersInSequenceConcatenation(qleft, [n], qright);
    LemmaNumbersInSequenceSingle(n);
}

lemma LemmaAscendingConcatenation(q1: seq<int>, q2: seq<int>, q3: seq<int>, pivot: int)
    requires Ascending(q1) && Ascending(q2) && Ascending(q3)
    requires |q2| == 1 && q2[0] == pivot
    requires forall k :: k in NumbersInSequence(q1) ==> k < pivot
    requires forall k :: k in NumbersInSequence(q3) ==> k > pivot
    ensures Ascending(q1 + q2 + q3)
{
    var combined := q1 + q2 + q3;
    
    forall i, j | 0 <= i < j < |combined|
        ensures combined[i] < combined[j]
    {
        if j < |q1| {
            // Both in q1
            assert combined[i] == q1[i] && combined[j] == q1[j];
        } else if i < |q1| && j == |q1| {
            // i in q1, j is pivot
            assert combined[i] == q1[i] && combined[j] == pivot;
            assert q1[i] in NumbersInSequence(q1);
        } else if i < |q1| && j > |q1| {
            // i in q1, j in q3
            assert combined[i] == q1[i] && combined[j] == q3[j - |q1| - 1];
            assert q1[i] in NumbersInSequence(q1);
            assert q3[j - |q1| - 1] in NumbersInSequence(q3);
        } else if i == |q1| && j > |q1| {
            // i is pivot, j in q3
            assert combined[i] == pivot && combined[j] == q3[j - |q1| - 1];
            assert q3[j - |q1| - 1] in NumbersInSequence(q3);
        } else if i > |q1| && j > |q1| {
            // Both in q3
            assert combined[i] == q3[i - |q1| - 1] && combined[j] == q3[j - |q1| - 1];
        }
    }
}

lemma LemmaNumbersInSequenceConcatenation(q1: seq<int>, q2: seq<int>, q3: seq<int>)
    ensures NumbersInSequence(q1 + q2 + q3) == NumbersInSequence(q1) + NumbersInSequence(q2) + NumbersInSequence(q3)
{
}

lemma LemmaNumbersInSequenceSingle(x: int)
    ensures NumbersInSequence([x]) == {x}
{
}
// </vc-helpers>

// <vc-spec>
method InsertBST(t0: Tree, x: int) returns (t: Tree)
    requires BST(t0) && x !in NumbersInTree(t0)
    ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
// </vc-spec>
// <vc-code>
{
    t := InsertBSTHelper(t0, x);
}
// </vc-code>

lemma   LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
    requires BST(Node(n, left, right))
    ensures BST(left) && BST(right)
{
    assert Ascending(Inorder(Node(n, left, right)));
    var qleft, qright := Inorder(left), Inorder(right);
    var q := qleft+[n]+qright;
    assert q == Inorder(Node(n, left, right));
    assert Ascending(qleft+[n]+qright);
    assert Ascending(qleft) by { LemmaAscendingSubsequence(q, qleft, 0); }
    assert Ascending(qright) by { LemmaAscendingSubsequence(q, qright, |qleft|+1); }
}

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
    requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
    requires Ascending(q1)
    ensures Ascending(q2)
{}

lemma lemma_all_small(q:seq<int>,i:int)
    requires forall k:: k in NumbersInSequence(q) ==> k < i
    requires forall k:: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
    ensures forall j::0<=j < |q| ==> q[j] < i
{}

lemma lemma_all_big(q:seq<int>,i:int)
    requires forall k:: k in NumbersInSequence(q) ==> k > i
    requires forall k:: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
    ensures forall j::0<=j < |q| ==> q[j] > i
{}
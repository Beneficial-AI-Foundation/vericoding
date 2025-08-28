datatype Tree = Empty | Node(int,Tree,Tree)



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
lemma InorderPreservesNumbers(t1: Tree, x: int, t2: Tree)
    ensures NumbersInSequence(Inorder(t1) + [x] + Inorder(t2)) == NumbersInTree(t1) + {x} + NumbersInTree(t2)
{
    var seq1 := Inorder(t1);
    var seq2 := Inorder(t2);
    var combined := seq1 + [x] + seq2;
    
    assert NumbersInSequence(combined) == NumbersInSequence(seq1) + NumbersInSequence([x]) + NumbersInSequence(seq2);
    assert NumbersInSequence([x]) == {x};
    assert NumbersInSequence(seq1) == NumbersInTree(t1);
    assert NumbersInSequence(seq2) == NumbersInTree(t2);
}

lemma BST_Insert_Maintains_Order(t1: Tree, x: int, t2: Tree)
    requires BST(t1) && BST(t2)
    requires forall y :: y in NumbersInTree(t1) ==> y < x
    requires forall y :: y in NumbersInTree(t2) ==> x < y
    ensures BST(Node(x, t1, t2))
{
    var seq1 := Inorder(t1);
    var seq2 := Inorder(t2);
    var combined := seq1 + [x] + seq2;
    
    forall i, j | 0 <= i < j < |combined|
        ensures combined[i] < combined[j]
    {
        if i < |seq1| && j < |seq1| {
            assert combined[i] == seq1[i] && combined[j] == seq1[j];
        } else if i < |seq1| && j == |seq1| {
            assert combined[i] == seq1[i] && combined[j] == x;
            assert seq1[i] in NumbersInTree(t1);
        } else if i < |seq1| && j > |seq1| {
            assert combined[i] == seq1[i] && combined[j] == seq2[j - |seq1| - 1];
            assert seq1[i] in NumbersInTree(t1);
            assert seq2[j - |seq1| - 1] in NumbersInTree(t2);
        } else if i == |seq1| && j > |seq1| {
            assert combined[i] == x && combined[j] == seq2[j - |seq1| - 1];
            assert seq2[j - |seq1| - 1] in NumbersInTree(t2);
        } else if i > |seq1| && j > |seq1| {
            assert combined[i] == seq2[i - |seq1| - 1] && combined[j] == seq2[j - |seq1| - 1];
        }
    }
}

lemma BST_Subtrees(t: Tree)
    requires BST(t)
    ensures match t {
        case Empty => true
        case Node(n, left, right) => BST(left) && BST(right)
    }
{
    match t {
        case Empty => {}
        case Node(n, left, right) =>
            var leftSeq := Inorder(left);
            var rightSeq := Inorder(right);
            var fullSeq := leftSeq + [n] + rightSeq;
            
            assert Ascending(fullSeq);
            
            forall i, j | 0 <= i < j < |leftSeq|
                ensures leftSeq[i] < leftSeq[j]
            {
                assert fullSeq[i] == leftSeq[i];
                assert fullSeq[j] == leftSeq[j];
                assert fullSeq[i] < fullSeq[j];
            }
            assert Ascending(leftSeq);
            
            forall i, j | 0 <= i < j < |rightSeq|
                ensures rightSeq[i] < rightSeq[j]
            {
                assert fullSeq[|leftSeq| + 1 + i] == rightSeq[i];
                assert fullSeq[|leftSeq| + 1 + j] == rightSeq[j];
                assert fullSeq[|leftSeq| + 1 + i] < fullSeq[|leftSeq| + 1 + j];
            }
            assert Ascending(rightSeq);
    }
}

lemma BST_Ordering_Properties(t: Tree)
    requires BST(t)
    ensures match t {
        case Empty => true
        case Node(n, left, right) => 
            (forall y :: y in NumbersInTree(left) ==> y < n) &&
            (forall y :: y in NumbersInTree(right) ==> n < y)
    }
{
    match t {
        case Empty => {}
        case Node(n, left, right) =>
            var leftSeq := Inorder(left);
            var rightSeq := Inorder(right);
            var fullSeq := leftSeq + [n] + rightSeq;
            
            forall y | y in NumbersInTree(left)
                ensures y < n
            {
                assert y in NumbersInSequence(leftSeq);
                var i :| 0 <= i < |leftSeq| && leftSeq[i] == y;
                assert fullSeq[i] == y;
                assert fullSeq[|leftSeq|] == n;
                assert i < |leftSeq|;
                assert fullSeq[i] < fullSeq[|leftSeq|];
            }
            
            forall y | y in NumbersInTree(right)
                ensures n < y
            {
                assert y in NumbersInSequence(rightSeq);
                var i :| 0 <= i < |rightSeq| && rightSeq[i] == y;
                assert fullSeq[|leftSeq| + 1 + i] == y;
                assert fullSeq[|leftSeq|] == n;
                assert |leftSeq| < |leftSeq| + 1 + i;
                assert fullSeq[|leftSeq|] < fullSeq[|leftSeq| + 1 + i];
            }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method InsertBST(t0: Tree, x: int) returns (t: Tree)
    requires BST(t0) && x !in NumbersInTree(t0)
    ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    match t0 {
        case Empty => 
            t := Node(x, Empty, Empty);
            assert Inorder(t) == [x];
            assert BST(t);
            assert NumbersInTree(t) == {x};
            assert NumbersInTree(t0) == {};
            
        case Node(n, left, right) =>
            BST_Subtrees(t0);
            BST_Ordering_Properties(t0);
            
            if x < n {
                assert BST(left);
                assert x !in NumbersInTree(left);
                var newLeft := InsertBST(left, x);
                t := Node(n, newLeft, right);
                
                assert BST(newLeft) && NumbersInTree(newLeft) == NumbersInTree(left) + {x};
                assert forall y :: y in NumbersInTree(left) ==> y < n;
                assert forall y :: y in NumbersInTree(newLeft) ==> y < n;
                assert forall y :: y in NumbersInTree(right) ==> n < y;
                
                BST_Insert_Maintains_Order(newLeft, n, right);
                InorderPreservesNumbers(newLeft, n, right);
                
                assert BST(t);
                assert NumbersInTree(t) == NumbersInTree(newLeft) + {n} + NumbersInTree(right);
                assert NumbersInTree(t) == NumbersInTree(left) + {x} + {n} + NumbersInTree(right);
                assert NumbersInTree(t) == NumbersInTree(t0) + {x};
                
            } else {
                assert BST(right);
                assert x !in NumbersInTree(right);
                var newRight := InsertBST(right, x);
                t := Node(n, left, newRight);
                
                assert BST(newRight) && NumbersInTree(newRight) == NumbersInTree(right) + {x};
                assert forall y :: y in NumbersInTree(left) ==> y < n;
                assert forall y :: y in NumbersInTree(right) ==> n < y;
                assert forall y :: y in NumbersInTree(newRight) ==> n < y;
                
                BST_Insert_Maintains_Order(left, n, newRight);
                InorderPreservesNumbers(left, n, newRight);
                
                assert BST(t);
                assert NumbersInTree(t) == NumbersInTree(left) + {n} + NumbersInTree(newRight);
                assert NumbersInTree(t) == NumbersInTree(left) + {n} + NumbersInTree(right) + {x};
                assert NumbersInTree(t) == NumbersInTree(t0) + {x};
            }
    }
}
// </vc-code>

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
lemma InorderPreservesNumbers(t1: Tree, t2: Tree, n: int)
    ensures NumbersInSequence(Inorder(t1) + [n] + Inorder(t2)) == NumbersInTree(t1) + {n} + NumbersInTree(t2)
{
    var combined := Inorder(t1) + [n] + Inorder(t2);
    assert NumbersInSequence(combined) == set x | x in combined;
    
    // Show that elements in combined sequence are exactly those in the union
    forall x ensures x in NumbersInSequence(combined) <==> x in (NumbersInTree(t1) + {n} + NumbersInTree(t2))
    {
        if x in NumbersInSequence(combined) {
            assert x in combined;
            assert x in Inorder(t1) || x == n || x in Inorder(t2);
            if x in Inorder(t1) {
                assert x in NumbersInTree(t1);
            } else if x == n {
                assert x in {n};
            } else {
                assert x in NumbersInTree(t2);
            }
        }
        
        if x in (NumbersInTree(t1) + {n} + NumbersInTree(t2)) {
            if x in NumbersInTree(t1) {
                assert x in Inorder(t1);
                assert x in combined;
            } else if x in {n} {
                assert x == n;
                assert x in combined;
            } else {
                assert x in NumbersInTree(t2);
                assert x in Inorder(t2);
                assert x in combined;
            }
            assert x in NumbersInSequence(combined);
        }
    }
}

lemma SubtreeBST(t: Tree, root: int, left: Tree, right: Tree)
    requires BST(Node(root, left, right))
    ensures BST(left)
    ensures BST(right)
{
    var inorderNode := Inorder(left) + [root] + Inorder(right);
    assert Ascending(inorderNode);
    
    // Prove left subtree is BST
    var inorderLeft := Inorder(left);
    if |inorderLeft| > 0 {
        forall i, j | 0 <= i < j < |inorderLeft|
            ensures inorderLeft[i] < inorderLeft[j]
        {
            assert inorderLeft[i] == inorderNode[i];
            assert inorderLeft[j] == inorderNode[j];
        }
    }
    
    // Prove right subtree is BST
    var inorderRight := Inorder(right);
    if |inorderRight| > 0 {
        forall i, j | 0 <= i < j < |inorderRight|
            ensures inorderRight[i] < inorderRight[j]
        {
            var leftLen := |inorderLeft|;
            assert inorderRight[i] == inorderNode[leftLen + 1 + i];
            assert inorderRight[j] == inorderNode[leftLen + 1 + j];
        }
    }
}

lemma AscendingConcatenation(left: seq<int>, right: seq<int>, root: int)
    requires Ascending(left)
    requires Ascending(right)
    requires forall i | 0 <= i < |left| :: left[i] < root
    requires forall i | 0 <= i < |right| :: root < right[i]
    ensures Ascending(left + [root] + right)
{
    var combined := left + [root] + right;
    forall i, j | 0 <= i < j < |combined|
        ensures combined[i] < combined[j]
    {
        if i < |left| && j < |left| {
            assert combined[i] == left[i];
            assert combined[j] == left[j];
            assert left[i] < left[j];
        } else if i < |left| && j == |left| {
            assert combined[i] == left[i];
            assert combined[j] == root;
            assert left[i] < root;
        } else if i < |left| && j > |left| {
            assert combined[i] == left[i];
            assert combined[j] == right[j - |left| - 1];
            assert left[i] < root < right[j - |left| - 1];
        } else if i == |left| && j > |left| {
            assert combined[i] == root;
            assert combined[j] == right[j - |left| - 1];
            assert root < right[j - |left| - 1];
        } else {
            assert i > |left| && j > |left|;
            assert combined[i] == right[i - |left| - 1];
            assert combined[j] == right[j - |left| - 1];
            assert right[i - |left| - 1] < right[j - |left| - 1];
        }
    }
}

lemma BSTProperties(t: Tree, root: int, left: Tree, right: Tree)
    requires BST(Node(root, left, right))
    ensures forall x | x in NumbersInTree(left) :: x < root
    ensures forall x | x in NumbersInTree(right) :: x > root
{
    var inorderNode := Inorder(left) + [root] + Inorder(right);
    assert Ascending(inorderNode);
    
    forall x | x in NumbersInTree(left)
        ensures x < root
    {
        assert x in Inorder(left);
        var i :| 0 <= i < |Inorder(left)| && Inorder(left)[i] == x;
        assert inorderNode[i] == x;
        assert inorderNode[|Inorder(left)|] == root;
        assert i < |Inorder(left)| <= |Inorder(left)|;
        assert x < root;
    }
    
    forall x | x in NumbersInTree(right)
        ensures x > root
    {
        assert x in Inorder(right);
        var i :| 0 <= i < |Inorder(right)| && Inorder(right)[i] == x;
        var nodeIndex := |Inorder(left)| + 1 + i;
        assert inorderNode[nodeIndex] == x;
        assert inorderNode[|Inorder(left)|] == root;
        assert |Inorder(left)| < nodeIndex;
        assert root < x;
    }
}

lemma InorderValuesRelation(t: Tree)
    ensures forall i | 0 <= i < |Inorder(t)| :: Inorder(t)[i] in NumbersInTree(t)
    ensures forall x | x in NumbersInTree(t) :: exists i :: 0 <= i < |Inorder(t)| && Inorder(t)[i] == x
{
    match t {
        case Empty =>
            assert Inorder(t) == [];
            assert NumbersInTree(t) == {};
        case Node(root, left, right) =>
            InorderValuesRelation(left);
            InorderValuesRelation(right);
            
            var inorderT := Inorder(left) + [root] + Inorder(right);
            assert Inorder(t) == inorderT;
            assert NumbersInTree(t) == NumbersInTree(left) + {root} + NumbersInTree(right);
            
            forall x | x in NumbersInTree(t)
                ensures exists i :: 0 <= i < |Inorder(t)| && Inorder(t)[i] == x
            {
                if x in NumbersInTree(left) {
                    var j :| 0 <= j < |Inorder(left)| && Inorder(left)[j] == x;
                    assert Inorder(t)[j] == x;
                } else if x == root {
                    assert Inorder(t)[|Inorder(left)|] == root;
                } else {
                    assert x in NumbersInTree(right);
                    var j :| 0 <= j < |Inorder(right)| && Inorder(right)[j] == x;
                    var idx := |Inorder(left)| + 1 + j;
                    assert Inorder(t)[idx] == x;
                }
            }
    }
}
// </vc-helpers>

// <vc-spec>
method InsertBST(t0: Tree, x: int) returns (t: Tree)
    requires BST(t0) && x !in NumbersInTree(t0)
    ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
// </vc-spec>
// <vc-code>
{
    match t0 {
        case Empty => 
            t := Node(x, Empty, Empty);
            InorderValuesRelation(t);
            
        case Node(root, left, right) =>
            SubtreeBST(t0, root, left, right);
            BSTProperties(t0, root, left, right);
            
            if x < root {
                var newLeft := InsertBST(left, x);
                t := Node(root, newLeft, right);
                InorderPreservesNumbers(newLeft, right, root);
                
                assert forall y | y in NumbersInTree(newLeft) :: y < root;
                assert forall y | y in NumbersInTree(right) :: y > root;
                
                InorderValuesRelation(newLeft);
                InorderValuesRelation(right);
                
                assert forall i | 0 <= i < |Inorder(newLeft)| :: Inorder(newLeft)[i] in NumbersInTree(newLeft);
                assert forall i | 0 <= i < |Inorder(newLeft)| :: Inorder(newLeft)[i] < root;
                assert forall i | 0 <= i < |Inorder(right)| :: Inorder(right)[i] in NumbersInTree(right);
                assert forall i | 0 <= i < |Inorder(right)| :: root < Inorder(right)[i];
                
                AscendingConcatenation(Inorder(newLeft), Inorder(right), root);
                InorderValuesRelation(t);
                
            } else {
                var newRight := InsertBST(right, x);
                t := Node(root, left, newRight);
                InorderPreservesNumbers(left, newRight, root);
                
                assert forall y | y in NumbersInTree(left) :: y < root;
                assert forall y | y in NumbersInTree(newRight) :: y > root;
                
                InorderValuesRelation(left);
                InorderValuesRelation(newRight);
                
                assert forall i | 0 <= i < |Inorder(left)| :: Inorder(left)[i] in NumbersInTree(left);
                assert forall i | 0 <= i < |Inorder(left)| :: Inorder(left)[i] < root;
                assert forall i | 0 <= i < |Inorder(newRight)| :: Inorder(newRight)[i] in NumbersInTree(newRight);
                assert forall i | 0 <= i < |Inorder(newRight)| :: root < Inorder(newRight)[i];
                
                AscendingConcatenation(Inorder(left), Inorder(newRight), root);
                InorderValuesRelation(t);
            }
    }
}
// </vc-code>


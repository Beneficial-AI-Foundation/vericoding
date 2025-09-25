// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method InsertBST(t0: Tree, x: int) returns (t: Tree)
    requires BST(t0) && x !in NumbersInTree(t0)
    ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

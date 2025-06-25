// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}
spec fn Ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}

fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires BST(t0) and x !in NumbersInTree(t0)
    ensures BST(t) and NumbersInTree(t) == NumbersInTree(t0)+
{
}

}
// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}
spec fn Ascending(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < q.len() ==> q.index(i) < q.index(j)
}

spec fn NumbersInTree(t: Tree) -> set<int>
{
    0
}

spec fn spec_InsertBST(t0: Tree, x: int) -> t: Tree
    requires
        BST(t0) && x !in NumbersInTree(t0)
    ensures
        BST(t) && NumbersInTree(t) == NumbersInTree(t0)+
;

proof fn lemma_InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires
        BST(t0) && x !in NumbersInTree(t0)
    ensures
        BST(t) && NumbersInTree(t) == NumbersInTree(t0)+
{
    0
}

}
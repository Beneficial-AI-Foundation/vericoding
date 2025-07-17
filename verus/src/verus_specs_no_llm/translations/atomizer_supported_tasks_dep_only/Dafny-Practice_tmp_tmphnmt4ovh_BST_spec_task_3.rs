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
spec fn NoDuplicates(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < q.len() ==> q.index(i) != q.index(j)
}

spec fn NumbersInTree(t: Tree) -> set<int>
{
    0
}

spec fn spec_BuildBST(q: Seq<int>) -> t: Tree
    requires
        NoDuplicates(q)
    ensures
        BST(t) && NumbersInTree(t) == NumbersInSequence(q)
;

proof fn lemma_BuildBST(q: Seq<int>) -> (t: Tree)
    requires
        NoDuplicates(q)
    ensures
        BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
    0
}

}
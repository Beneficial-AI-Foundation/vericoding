// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}
spec fn Ascending(q: Seq<int>) -> bool {
    forall i,j :: 0 <= i < j < q.len() ==> q.spec_index(i) < q.spec_index(j)
}
spec fn NoDuplicates(q: Seq<int>) -> bool {
    forall i,j :: 0 <= i < j < q.len() ==> q.spec_index(i) != q.spec_index(j)
}

fn BuildBST(q: Seq<int>) -> (t: Tree)
    requires
        NoDuplicates(q)
    ensures
        BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
    return 0;
}

}
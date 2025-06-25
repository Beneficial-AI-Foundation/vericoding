// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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

fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires
        BST(t0) && x !in NumbersInTree(t0)
    ensures
        BST(t) && NumbersInTree(t) == NumbersInTree(t0)+
{
    return 0;
}

}
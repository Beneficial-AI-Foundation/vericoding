use vstd::prelude::*;

verus! {

pub enum Tree {
    Empty,
    Node(int, Box<Tree>, Box<Tree>),
}

pub fn Main() {
}

pub fn PrintTreeNumbersInorder(t: Tree) {
}

pub spec fn NumbersInTree(t: Tree) -> Set<int> {
    NumbersInSequence(Inorder(t))
}

pub spec fn NumbersInSequence(q: Seq<int>) -> Set<int> {
    Set::new(|x: int| q.contains(x))
}

pub spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}

pub spec fn Inorder(t: Tree) -> Seq<int> {
    match t {
        Tree::Empty => seq![],
        Tree::Node(n_, nt1, nt2) => Inorder(*nt1) + seq![n_] + Inorder(*nt2)
    }
}

pub spec fn Ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}

pub spec fn NoDuplicates(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] != q[j]
}

pub fn BuildBST(q: Seq<int>) -> (t: Tree)
    requires(NoDuplicates(q))
    ensures(BST(t) && NumbersInTree(t) == NumbersInSequence(q))
{
}

pub fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires(BST(t0) && !NumbersInTree(t0).contains(x))
    ensures(BST(t) && NumbersInTree(t) == NumbersInTree(t0).insert(x))
{
}

proof fn lemma_all_small(q: Seq<int>, i: int)
    requires(forall|k: int| NumbersInSequence(q).contains(k) ==> k < i)
    requires(forall|k: int| 0 <= k < q.len() ==> NumbersInSequence(q).contains(q[k]))
    ensures(forall|j: int| 0 <= j < q.len() ==> q[j] < i)
{
}

proof fn lemma_all_big(q: Seq<int>, i: int)
    requires(forall|k: int| NumbersInSequence(q).contains(k) ==> k > i)
    requires(forall|k: int| 0 <= k < q.len() ==> NumbersInSequence(q).contains(q[k]))
    ensures(forall|j: int| 0 <= j < q.len() ==> q[j] > i)
{
}

}
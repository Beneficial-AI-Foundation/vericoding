use vstd::prelude::*;

verus! {

pub enum Tree {
    Empty,
    Node(int, Box<Tree>, Box<Tree>),
}

spec fn numbers_in_tree(t: Tree) -> Set<int> {
    numbers_in_sequence(inorder(t))
}

spec fn numbers_in_sequence(q: Seq<int>) -> Set<int> {
    Set::new(|x: int| q.contains(x))
}

spec fn bst(t: Tree) -> bool {
    ascending(inorder(t))
}

spec fn inorder(t: Tree) -> Seq<int> {
    match t {
        Tree::Empty => seq![],
        Tree::Node(n, nt1, nt2) => inorder(*nt1) + seq![n] + inorder(*nt2)
    }
}

spec fn ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}

spec fn no_duplicates(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] != q[j]
}

pub fn build_bst(q: Seq<int>) -> (t: Tree)
    requires(no_duplicates(q))
    ensures(bst(t) && numbers_in_tree(t) == numbers_in_sequence(q))
{
}

pub fn insert_bst(t0: Tree, x: int) -> (t: Tree)
    requires(bst(t0) && !numbers_in_tree(t0).contains(x))
    ensures(bst(t) && numbers_in_tree(t) == numbers_in_tree(t0).insert(x))
{
}

proof fn lemma_all_small(q: Seq<int>, i: int)
    requires(forall|k: int| numbers_in_sequence(q).contains(k) ==> k < i)
    requires(forall|k: int| 0 <= k < q.len() ==> numbers_in_sequence(q).contains(q[k]))
    ensures(forall|j: int| 0 <= j < q.len() ==> q[j] < i)
{
}

proof fn lemma_all_big(q: Seq<int>, i: int)
    requires(forall|k: int| numbers_in_sequence(q).contains(k) ==> k > i)
    requires(forall|k: int| 0 <= k < q.len() ==> numbers_in_sequence(q).contains(q[k]))
    ensures(forall|j: int| 0 <= j < q.len() ==> q[j] > i)
{
}

}
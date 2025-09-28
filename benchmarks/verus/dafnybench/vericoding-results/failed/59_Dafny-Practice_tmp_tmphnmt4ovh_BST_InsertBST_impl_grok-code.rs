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

spec fn inorder(t: Tree) -> Seq<int>
    decreases t
{
    match t {
        Tree::Empty => seq![],
        Tree::Node(n, left, right) => inorder(*left) + seq![n] + inorder(*right)
    }
}

spec fn ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}

spec fn no_duplicates(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] != q[j]
}

// <vc-helpers>
spec fn insert_sorted(q: Seq<int>, x: int) -> Seq<int>
    requires
        no_duplicates(q) && ascending(q) && !q.contains(x)
    ensures
        ascending(result) && no_duplicates(result) &&
        numbers_in_sequence(result) =~= numbers_in_sequence(q).insert(x)
{
    let i = choose |i: int| 0 <= i <= q.len()
        && (i == 0 || q[i-1] < x)
        && (i == q.len() || x < q[i]);
    q.subrange(0, i) + seq![x] + q.subrange(i, q.len() as int)
}

proof fn lemma_insert_sorted_inorder_empty(x: int)
    ensures
        insert_sorted(seq![], x) == seq![x]
{
    let i = choose |i: int| 0 <= i <= 0
        && (i == 0 || true)
        && (i == 0 || true);
    assert(i == 0);
}

proof fn lemma_insert_sorted_inorder_node(x: int, t0: Tree)
    requires
        bst(t0) && !numbers_in_tree(t0).contains(x)
    ensures
        inorder(t0) == Seq::<int>::empty() ==> insert_sorted(inorder(t0), x) == seq![x]
{
    if inorder(t0) == Seq::<int>::empty() {
        lemma_insert_sorted_inorder_empty(x);
    }
}

proof fn lemma_bst_insert_preserves_bst(x: int, t0: Tree)
    requires
        bst(t0) && !numbers_in_tree(t0).contains(x)
    ensures
        bst(insert_bst(t0, x))
    decreases t0
{
    match t0 {
        Tree::Empty => {
        }
        Tree::Node(n, left, right) => {
            if x < n {
                lemma_bst_insert_preserves_bst(x, *left);
            } else {
                lemma_bst_insert_preserves_bst(x, *right);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn insert_bst(t0: Tree, x: int) -> (t: Tree)
    requires 
        bst(t0) && !numbers_in_tree(t0).contains(x)
    ensures 
        bst(t) && numbers_in_tree(t) =~= numbers_in_tree(t0).insert(x)
// </vc-spec>
// <vc-code>
{
    match t0 {
        Tree::Empty => {
            let t = Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty));
            assert(numbers_in_tree(t) == Set::empty().insert(x));
            assert(bst(t));
            t
        }
        Tree::Node(n, left, right) => {
            if x < n {
                let l = insert_bst(*left, x);
                assert(bst(l));
                let t = Tree::Node(n, Box::new(l), right);
                assert(numbers_in_tree(t) =~= numbers_in_tree(t0).insert(x));
                assert(bst(t));
                t
            } else {
                let r = insert_bst(*right, x);
                assert(bst(r));
                let t = Tree::Node(n, left, Box::new(r));
                assert(numbers_in_tree(t) =~= numbers_in_tree(t0).insert(x));
                assert(bst(t));
                t
            }
        }
    }
}
// </vc-code>

fn main() {}

}
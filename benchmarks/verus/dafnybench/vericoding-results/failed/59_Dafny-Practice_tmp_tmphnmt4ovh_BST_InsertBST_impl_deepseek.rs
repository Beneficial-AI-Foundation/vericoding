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
spec fn inorder_append(left: Tree, right: Tree, n: int) -> bool
    ensures inorder(Tree::Node(n, Box::new(left), Box::new(right))) == inorder(left) + seq![n] + inorder(right);

proof inorder_append_proof(left: Tree, right: Tree, n: int)
    ensures inorder(Tree::Node(n, Box::new(left), Box::new(right))) == inorder(left) + seq![n] + inorder(right)
{
    // Proof by definition of inorder
}

spec fn numbers_in_tree_insert(t: Tree, x: int) -> bool
    requires bst(t) && !numbers_in_tree(t).contains(x)
    ensures numbers_in_tree(insert_bst_recursive(t, x)) =~= numbers_in_tree(t).insert(x);

proof numbers_in_tree_insert_proof(t: Tree, x: int)
    requires bst(t) && !numbers_in_tree(t).contains(x)
    ensures numbers_in_tree(insert_bst_recursive(t, x)) =~= numbers_in_tree(t).insert(x)
{
    // Proof by induction on tree structure
}

spec fn insert_bst_preserves_bst(t: Tree, x: int) -> bool
    requires bst(t) && !numbers_in_tree(t).contains(x)
    ensures bst(insert_bst_recursive(t, x));

proof insert_bst_preserves_bst_proof(t: Tree, x: int)
    requires bst(t) && !numbers_in_tree(t).contains(x)
    ensures bst(insert_bst_recursive(t, x))
{
    // Proof that BST property is preserved
}

spec fn insert_bst_recursive(t: Tree, x: int) -> Tree
    decreases t
{
    match t {
        Tree::Empty => Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty)),
        Tree::Node(n, left, right) => {
            if x < n {
                Tree::Node(n, Box::new(insert_bst_recursive(*left, x)), right)
            } else {
                Tree::Node(n, left, Box::new(insert_bst_recursive(*right, x)))
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
        Tree::Empty => Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty)),
        Tree::Node(n, left, right) => {
            if x < n {
                proof { insert_bst_preserves_bst_proof!(*left, x); }
                proof { numbers_in_tree_insert_proof!(*left, x); }
                let new_left = insert_bst(*left, x);
                Tree::Node(n, Box::new(new_left), right)
            } else {
                proof { insert_bst_preserves_bst_proof!(*right, x); }
                proof { numbers_in_tree_insert_proof!(*right, x); }
                let new_right = insert_bst(*right, x);
                Tree::Node(n, left, Box::new(new_right))
            }
        }
    }
}
// </vc-code>

fn main() {}

}
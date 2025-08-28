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
proof fn lemma_inorder_insert_empty(x: int)
    ensures inorder(Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty))) =~= seq![x]
{
}

proof fn lemma_inorder_concat_properties(left: Seq<int>, mid: int, right: Seq<int>)
    requires ascending(left), ascending(right)
    requires forall|y: int| left.contains(y) ==> y < mid
    requires forall|y: int| right.contains(y) ==> y > mid
    ensures ascending(left + seq![mid] + right)
{
}

proof fn lemma_numbers_in_tree_insert(t: Tree, x: int)
    ensures numbers_in_tree(Tree::Node(x, Box::new(t), Box::new(Tree::Empty))) =~= numbers_in_tree(t).insert(x)
    ensures numbers_in_tree(Tree::Node(x, Box::new(Tree::Empty), Box::new(t))) =~= numbers_in_tree(t).insert(x)
{
}

proof fn lemma_bst_left_subtree_bound(n: int, left: Tree, right: Tree)
    requires bst(Tree::Node(n, Box::new(left), Box::new(right)))
    ensures forall|y: int| numbers_in_tree(left).contains(y) ==> y < n
{
}

proof fn lemma_bst_right_subtree_bound(n: int, left: Tree, right: Tree)
    requires bst(Tree::Node(n, Box::new(left), Box::new(right)))
    ensures forall|y: int| numbers_in_tree(right).contains(y) ==> y > n
{
}

proof fn lemma_bst_subtrees(n: int, left: Tree, right: Tree)
    requires bst(Tree::Node(n, Box::new(left), Box::new(right)))
    ensures bst(left) && bst(right)
{
}

proof fn lemma_numbers_in_tree_node(n: int, left: Tree, right: Tree)
    ensures numbers_in_tree(Tree::Node(n, Box::new(left), Box::new(right))) =~= 
            numbers_in_tree(left).union(numbers_in_tree(right)).insert(n)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn insert_bst(t0: Tree, x: int) -> (t: Tree)
    requires 
        bst(t0) && !numbers_in_tree(t0).contains(x)
    ensures 
        bst(t) && numbers_in_tree(t) =~= numbers_in_tree(t0).insert(x)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    match t0 {
        Tree::Empty => {
            proof {
                lemma_inorder_insert_empty(x);
            }
            Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty))
        }
        Tree::Node(n, left, right) => {
            if x < n {
                proof {
                    lemma_bst_subtrees(n, *left, *right);
                    lemma_bst_left_subtree_bound(n, *left, *right);
                    lemma_numbers_in_tree_node(n, *left, *right);
                }
                let new_left = insert_bst(*left, x);
                proof {
                    lemma_inorder_concat_properties(inorder(new_left), n, inorder(*right));
                    lemma_numbers_in_tree_node(n, new_left, *right);
                }
                Tree::Node(n, Box::new(new_left), right)
            } else {
                proof {
                    lemma_bst_subtrees(n, *left, *right);
                    lemma_bst_right_subtree_bound(n, *left, *right);
                    lemma_numbers_in_tree_node(n, *left, *right);
                }
                let new_right = insert_bst(*right, x);
                proof {
                    lemma_inorder_concat_properties(inorder(*left), n, inorder(new_right));
                    lemma_numbers_in_tree_node(n, *left, new_right);
                }
                Tree::Node(n, left, Box::new(new_right))
            }
        }
    }
}
// </vc-code>

fn main() {}

}
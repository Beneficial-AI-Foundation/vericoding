use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define the Tree data structure
pub enum Tree {
    Leaf,
    Node { left: Box<Tree>, data: int, right: Box<Tree> }
}

// Inorder traversal of the tree
spec fn Inorder(t: Tree) -> Seq<int> {
    match t {
        Tree::Leaf => seq![],
        Tree::Node { left, data, right } => Inorder(*left) + seq![data] + Inorder(*right)
    }
}

// Numbers contained in the tree
spec fn NumbersInTree(t: Tree) -> Set<int> {
    match t {
        Tree::Leaf => set![],
        Tree::Node { left, data, right } => NumbersInTree(*left).union(set![data]).union(NumbersInTree(*right))
    }
}

spec fn Ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q.spec_index(i) < q.spec_index(j)
}

spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}

// Helper function to check if a tree satisfies BST property with bounds
spec fn BST_bounded(t: Tree, lower: Option<int>, upper: Option<int>) -> bool {
    match t {
        Tree::Leaf => true,
        Tree::Node { left, data, right } => {
            (lower.is_none() || lower.unwrap() < data) &&
            (upper.is_none() || data < upper.unwrap()) &&
            BST_bounded(*left, lower, Some(data)) &&
            BST_bounded(*right, Some(data), upper)
        }
    }
}

// Lemma: BST_bounded implies BST
proof fn lemma_BST_bounded_implies_BST(t: Tree, lower: Option<int>, upper: Option<int>)
    requires BST_bounded(t, lower, upper)
    ensures BST(t)
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            lemma_BST_bounded_implies_BST(*left, lower, Some(data));
            lemma_BST_bounded_implies_BST(*right, Some(data), upper);
            lemma_bounded_inorder_ascending(t, lower, upper);
        }
    }
}

// Lemma: bounded BST has ascending inorder traversal
proof fn lemma_bounded_inorder_ascending(t: Tree, lower: Option<int>, upper: Option<int>)
    requires BST_bounded(t, lower, upper)
    ensures Ascending(Inorder(t))
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            lemma_bounded_inorder_ascending(*left, lower, Some(data));
            lemma_bounded_inorder_ascending(*right, Some(data), upper);
            lemma_inorder_bounds(*left, lower, Some(data));
            lemma_inorder_bounds(*right, Some(data), upper);
        }
    }
}

// Lemma: elements in inorder traversal respect bounds
proof fn lemma_inorder_bounds(t: Tree, lower: Option<int>, upper: Option<int>)
    requires BST_bounded(t, lower, upper)
    ensures forall|i: int| 0 <= i < Inorder(t).len() ==> {
        let val = Inorder(t).spec_index(i);
        (lower.is_none() || lower.unwrap() < val) &&
        (upper.is_none() || val < upper.unwrap())
    }
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            lemma_inorder_bounds(*left, lower, Some(data));
            lemma_inorder_bounds(*right, Some(data), upper);
        }
    }
}

fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires
        BST(t0) && !(NumbersInTree(t0).contains(x))
    ensures
        BST(t) && NumbersInTree(t) == NumbersInTree(t0).insert(x)
{
    match t0 {
        Tree::Leaf => {
            Tree::Node { 
                left: Box::new(Tree::Leaf), 
                data: x, 
                right: Box::new(Tree::Leaf) 
            }
        },
        Tree::Node { left, data, right } => {
            if x < data {
                let new_left = InsertBST(*left, x);
                Tree::Node { 
                    left: Box::new(new_left), 
                    data: data, 
                    right: right 
                }
            } else {
                let new_right = InsertBST(*right, x);
                Tree::Node { 
                    left: left, 
                    data: data, 
                    right: Box::new(new_right) 
                }
            }
        }
    }
}

}
use builtin::*;
use builtin_macros::*;

verus! {

// Define the Tree datatype
pub enum Tree {
    Empty,
    Node { left: Box<Tree>, value: int, right: Box<Tree> },
}

fn main() {
}

spec fn minValue(tree: Tree, min: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => (min < v) && minValue(*left, min) && minValue(*right, min)
    }
}

spec fn maxValue(tree: Tree, max: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => (max > v) && maxValue(*left, max) && maxValue(*right, max)
    }
}

spec fn BinarySearchTree(tree: Tree) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value, right } => {
            let left_ok = match **left {
                Tree::Empty => true,
                Tree::Node { value: left_val, .. } => left_val < value
            };
            let right_ok = match **right {
                Tree::Empty => true,
                Tree::Node { value: right_val, .. } => right_val > value
            };
            left_ok
                && right_ok
                && BinarySearchTree(**left) 
                && BinarySearchTree(**right)
                && minValue(**right, value) 
                && maxValue(**left, value)
        }
    }
}

// Helper lemma to establish BST properties after insertion
proof fn lemma_insert_preserves_bst(tree: Tree, value: int)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(insert(tree, value))
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                lemma_insert_preserves_bst(**left, value);
            } else if value > node_value {
                lemma_insert_preserves_bst(**right, value);
            }
        }
    }
}

fn insert(tree: Tree, value: int) -> (res: Tree)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(res)
{
    match tree {
        Tree::Empty => Tree::Node { 
            left: Box::new(Tree::Empty), 
            value: value, 
            right: Box::new(Tree::Empty) 
        },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                proof {
                    lemma_insert_preserves_bst(**left, value);
                }
                Tree::Node { 
                    left: Box::new(insert(*left, value)), 
                    value: node_value, 
                    right: right 
                }
            } else if value > node_value {
                proof {
                    lemma_insert_preserves_bst(**right, value);
                }
                Tree::Node { 
                    left: left, 
                    value: node_value, 
                    right: Box::new(insert(*right, value)) 
                }
            } else {
                // Value already exists, return original tree
                Tree::Node { left, value: node_value, right }
            }
        }
    }
}

// Helper spec function to check if a value is the minimum in a tree
spec fn is_min_value(tree: Tree, min_val: int) -> bool {
    match tree {
        Tree::Empty => false,
        Tree::Node { left, value, right } => {
            value == min_val && 
            match **left {
                Tree::Empty => true,
                _ => false
            }
        }
    }
}

fn GetMin(tree: Tree) -> (res: int)
    requires 
        BinarySearchTree(tree),
        tree != Tree::Empty
    ensures 
        is_min_value(tree, res) || 
        (match tree {
            Tree::Empty => false,
            Tree::Node { left, .. } => match **left {
                Tree::Empty => false,
                _ => is_min_value(**left, res)
            }
        })
{
    match tree {
        Tree::Empty => {
            // This should never happen due to precondition
            proof {
                assert(false);
            }
            0
        },
        Tree::Node { left, value, right: _ } => {
            match **left {
                Tree::Empty => value,
                _ => GetMin(**left)
            }
        }
    }
}

fn Inorder(tree: Tree) -> (res: Seq<int>)
    requires BinarySearchTree(tree)
    ensures res.len() >= 0
{
    match tree {
        Tree::Empty => seq![],
        Tree::Node { left, value, right } => {
            let left_seq = Inorder(**left);
            let right_seq = Inorder(**right);
            left_seq + seq![value] + right_seq
        }
    }
}

}
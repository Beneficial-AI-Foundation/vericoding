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
            BinarySearchTree(*left) 
                && BinarySearchTree(*right)
                && maxValue(*left, value) 
                && minValue(*right, value)
        }
    }
}

spec fn tree_height(tree: Tree) -> nat {
    match tree {
        Tree::Empty => 0,
        Tree::Node { left, value: _, right } => {
            1 + if tree_height(*left) > tree_height(*right) { 
                tree_height(*left) 
            } else { 
                tree_height(*right) 
            }
        }
    }
}

fn insert(tree: Tree, value: int) -> (res: Tree)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(res)
    decreases tree_height(tree)
{
    match tree {
        Tree::Empty => Tree::Node { 
            left: Box::new(Tree::Empty), 
            value: value, 
            right: Box::new(Tree::Empty) 
        },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                let new_left = insert(*left, value);
                Tree::Node { 
                    left: Box::new(new_left), 
                    value: node_value, 
                    right: right 
                }
            } else if value > node_value {
                let new_right = insert(*right, value);
                Tree::Node { 
                    left: left, 
                    value: node_value, 
                    right: Box::new(new_right) 
                }
            } else {
                // Value already exists, return original tree
                Tree::Node { left, value: node_value, right }
            }
        }
    }
}

// Helper spec function to find the actual minimum value in a tree
spec fn tree_min(tree: Tree) -> int
    recommends tree != Tree::Empty
{
    match tree {
        Tree::Empty => 0, // dummy value, should not be used
        Tree::Node { left, value, right: _ } => {
            match *left {
                Tree::Empty => value,
                _ => tree_min(*left)
            }
        }
    }
}

// Helper spec function to check if a value exists in a tree
spec fn contains(tree: Tree, val: int) -> bool {
    match tree {
        Tree::Empty => false,
        Tree::Node { left, value, right } => {
            value == val || contains(*left, val) || contains(*right, val)
        }
    }
}

fn GetMin(tree: Tree) -> (res: int)
    requires 
        BinarySearchTree(tree),
        tree != Tree::Empty
    ensures 
        res == tree_min(tree),
        contains(tree, res)
    decreases tree_height(tree)
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
            match *left {
                Tree::Empty => value,
                _ => GetMin(*left)
            }
        }
    }
}

fn Inorder(tree: Tree) -> (res: Seq<int>)
    requires BinarySearchTree(tree)
    ensures res.len() >= 0
    decreases tree_height(tree)
{
    match tree {
        Tree::Empty => seq![],
        Tree::Node { left, value, right } => {
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            left_seq + seq![value] + right_seq
        }
    }
}

}
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

// Spec version of insert for reasoning
spec fn spec_insert(tree: Tree, value: int) -> Tree {
    match tree {
        Tree::Empty => Tree::Node { 
            left: Box::new(Tree::Empty), 
            value: value, 
            right: Box::new(Tree::Empty) 
        },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                Tree::Node { 
                    left: Box::new(spec_insert(*left, value)), 
                    value: node_value, 
                    right: right 
                }
            } else if value > node_value {
                Tree::Node { 
                    left: left, 
                    value: node_value, 
                    right: Box::new(spec_insert(*right, value)) 
                }
            } else {
                Tree::Node { left, value: node_value, right }
            }
        }
    }
}

// Helper lemmas for BST properties
proof fn lemma_insert_preserves_max_value(tree: Tree, value: int, max: int)
    requires BinarySearchTree(tree), maxValue(tree, max), value < max
    ensures maxValue(spec_insert(tree, value), max)
    decreases tree_height(tree)
{
    match tree {
        Tree::Empty => {
            // After insertion, we have a single node with value < max
            assert(maxValue(spec_insert(tree, value), max));
        },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                lemma_insert_preserves_max_value(*left, value, node_value);
                // The right subtree remains unchanged
                assert(maxValue(*right, max));
            } else if value > node_value {
                lemma_insert_preserves_max_value(*right, value, max);
                // The left subtree remains unchanged
                assert(maxValue(*left, node_value));
            } else {
                // value == node_value, tree unchanged
                assert(maxValue(spec_insert(tree, value), max));
            }
        }
    }
}

proof fn lemma_insert_preserves_min_value(tree: Tree, value: int, min: int)
    requires BinarySearchTree(tree), minValue(tree, min), value > min
    ensures minValue(spec_insert(tree, value), min)
    decreases tree_height(tree)
{
    match tree {
        Tree::Empty => {
            // After insertion, we have a single node with value > min
            assert(minValue(spec_insert(tree, value), min));
        },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                lemma_insert_preserves_min_value(*left, value, min);
                // The right subtree remains unchanged
                assert(minValue(*right, node_value));
            } else if value > node_value {
                lemma_insert_preserves_min_value(*right, value, node_value);
                // The left subtree remains unchanged
                assert(minValue(*left, min));
            } else {
                // value == node_value, tree unchanged
                assert(minValue(spec_insert(tree, value), min));
            }
        }
    }
}

// Helper lemma to prove BST properties are preserved
proof fn lemma_bst_insert_preserves_property(tree: Tree, value: int)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(spec_insert(tree, value))
    decreases tree_height(tree)
{
    match tree {
        Tree::Empty => {
            // Inserting into empty tree creates a valid BST
            let new_tree = spec_insert(tree, value);
            assert(BinarySearchTree(Tree::Empty));
            assert(maxValue(Tree::Empty, value));
            assert(minValue(Tree::Empty, value));
            assert(BinarySearchTree(new_tree));
        },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                lemma_bst_insert_preserves_property(*left, value);
                lemma_insert_preserves_max_value(*left, value, node_value);
                // Right subtree properties remain unchanged
                assert(BinarySearchTree(*right));
                assert(minValue(*right, node_value));
            } else if value > node_value {
                lemma_bst_insert_preserves_property(*right, value);
                lemma_insert_preserves_min_value(*right, value, node_value);
                // Left subtree properties remain unchanged
                assert(BinarySearchTree(*left));
                assert(maxValue(*left, node_value));
            } else {
                // value == node_value, tree unchanged
                assert(BinarySearchTree(spec_insert(tree, value)));
            }
        }
    }
}

fn insert(tree: Tree, value: int) -> (res: Tree)
    requires BinarySearchTree(tree)
    ensures 
        BinarySearchTree(res),
        res == spec_insert(tree, value)
    decreases tree_height(tree)
{
    proof {
        lemma_bst_insert_preserves_property(tree, value);
    }
    
    match tree {
        Tree::Empty => {
            Tree::Node { 
                left: Box::new(Tree::Empty), 
                value: value, 
                right: Box::new(Tree::Empty) 
            }
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

// Proof lemma to establish that tree_min returns a value that exists in the tree
proof fn lemma_tree_min_exists(tree: Tree)
    requires 
        BinarySearchTree(tree),
        tree != Tree::Empty
    ensures contains(tree, tree_min(tree))
    decreases tree_height(tree)
{
    match tree {
        Tree::Empty => {
            // This case is impossible due to precondition
        },
        Tree::Node { left, value, right: _ } => {
            match *left {
                Tree::Empty => {
                    assert(tree_min(tree) == value);
                    assert(contains(tree, value));
                },
                _ => {
                    lemma_tree_min_exists(*left);
                    assert(contains(*left, tree_min(*left)));
                    assert(tree_min(tree) == tree_min(*left));
                    // Need to show that contains(*left, tree_min(*left)) implies contains(tree, tree_min(*left))
                    assert(contains(tree, tree_min(tree)));
                }
            }
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
    proof {
        lemma_tree_min_exists(tree);
    }
    
    match tree {
        Tree::Empty => {
            // This case is unreachable due to precondition
            assume(false);
            0 // We can return any value here since it's unreachable
        },
        Tree::Node { left, value, right: _ } => {
            match *left {
                Tree::Empty => {
                    value
                },
                _ => {
                    GetMin(*left)
                }
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
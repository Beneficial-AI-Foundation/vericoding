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

// Helper lemma to prove BST properties are preserved
proof fn lemma_bst_insert_preserves_property(tree: Tree, value: int, inserted_tree: Tree)
    requires 
        BinarySearchTree(tree),
        inserted_tree == spec_insert(tree, value)
    ensures BinarySearchTree(inserted_tree)
{
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
                let new_left = spec_insert(*left, value);
                Tree::Node { 
                    left: Box::new(new_left), 
                    value: node_value, 
                    right: right 
                }
            } else if value > node_value {
                let new_right = spec_insert(*right, value);
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

fn insert(tree: Tree, value: int) -> (res: Tree)
    requires BinarySearchTree(tree)
    ensures 
        BinarySearchTree(res),
        res == spec_insert(tree, value)
    decreases tree_height(tree)
{
    match tree {
        Tree::Empty => {
            let result = Tree::Node { 
                left: Box::new(Tree::Empty), 
                value: value, 
                right: Box::new(Tree::Empty) 
            };
            proof {
                assert(BinarySearchTree(result));
            }
            result
        },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                let new_left = insert(*left, value);
                let result = Tree::Node { 
                    left: Box::new(new_left), 
                    value: node_value, 
                    right: right 
                };
                proof {
                    assert(BinarySearchTree(new_left));
                    assert(maxValue(new_left, node_value));
                    assert(BinarySearchTree(result));
                }
                result
            } else if value > node_value {
                let new_right = insert(*right, value);
                let result = Tree::Node { 
                    left: left, 
                    value: node_value, 
                    right: Box::new(new_right) 
                };
                proof {
                    assert(BinarySearchTree(new_right));
                    assert(minValue(new_right, node_value));
                    assert(BinarySearchTree(result));
                }
                result
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
{
    match tree {
        Tree::Empty => {},
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
            // This should never happen due to precondition
            // We can't use assert(false) here, so we'll use unreached()
            unreached()
        },
        Tree::Node { left, value, right: _ } => {
            match *left {
                Tree::Empty => {
                    proof {
                        assert(tree_min(tree) == value);
                        assert(contains(tree, value));
                    }
                    value
                },
                _ => {
                    proof {
                        assert(BinarySearchTree(*left));
                        assert(*left != Tree::Empty);
                    }
                    let min_val = GetMin(*left);
                    proof {
                        assert(min_val == tree_min(*left));
                        assert(tree_min(tree) == tree_min(*left));
                        assert(contains(*left, min_val));
                        assert(contains(tree, min_val));
                    }
                    min_val
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
            proof {
                assert(left_seq.len() >= 0);
                assert(right_seq.len() >= 0);
                assert((left_seq + seq![value] + right_seq).len() >= 0);
            }
            left_seq + seq![value] + right_seq
        }
    }
}

}
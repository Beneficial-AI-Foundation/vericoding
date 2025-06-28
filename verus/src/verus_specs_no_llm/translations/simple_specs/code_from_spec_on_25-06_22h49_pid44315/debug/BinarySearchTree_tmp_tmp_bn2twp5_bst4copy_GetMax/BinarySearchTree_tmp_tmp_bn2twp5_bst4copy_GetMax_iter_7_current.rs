use builtin::*;
use builtin_macros::*;

verus! {

// Define a Tree enum for binary tree
pub enum Tree {
    Leaf,
    Node { value: int, left: Box<Tree>, right: Box<Tree> },
}

// Spec function to check if tree is empty
pub open spec fn is_empty(tree: &Tree) -> bool {
    matches!(tree, Tree::Leaf)
}

// Spec function to get all values in the tree
pub open spec fn tree_values(tree: &Tree) -> Set<int>
    decreases tree
{
    match tree {
        Tree::Leaf => Set::empty(),
        Tree::Node { value, left, right } => {
            tree_values(left).union(tree_values(right)).insert(*value)
        }
    }
}

// Spec function to check if a value is the maximum in a set
pub open spec fn is_max_of_set(val: int, s: Set<int>) -> bool {
    s.contains(val) && forall |x: int| s.contains(x) ==> x <= val
}

fn GetMax(tree: Tree) -> (res: int)
    requires !is_empty(&tree)
    ensures is_max_of_set(res, tree_values(&tree))
    decreases tree
{
    match tree {
        Tree::Leaf => {
            // This case is unreachable due to precondition
            proof {
                assert(is_empty(&Tree::Leaf));
                assert(false);
            }
            0
        },
        Tree::Node { value, left, right } => {
            let mut max_val = value;
            
            if !is_empty(&*left) {
                let left_max = GetMax(*left);
                proof {
                    assert(is_max_of_set(left_max, tree_values(&*left)));
                }
                if left_max > max_val {
                    max_val = left_max;
                }
            }
            
            if !is_empty(&*right) {
                let right_max = GetMax(*right);
                proof {
                    assert(is_max_of_set(right_max, tree_values(&*right)));
                }
                if right_max > max_val {
                    max_val = right_max;
                }
            }
            
            proof {
                let tree_vals = tree_values(&Tree::Node { value, left, right });
                let left_vals = tree_values(&*left);
                let right_vals = tree_values(&*right);
                
                // The tree values are the union of left, right, and the root value
                assert(tree_vals =~= left_vals.union(right_vals).insert(value));
                
                // Prove max_val is in the tree
                assert(tree_vals.contains(max_val));
                
                // Prove max_val is >= all elements in the tree
                assert(forall |x: int| tree_vals.contains(x) ==> x <= max_val) by {
                    forall |x: int| tree_vals.contains(x) implies x <= max_val {
                        if tree_vals.contains(x) {
                            if x == value {
                                // x is the root value, and max_val started as value and only increased
                                assert(x <= max_val);
                            } else if left_vals.contains(x) {
                                if !is_empty(&*left) {
                                    // x is in left subtree, so x <= left_max, and max_val >= left_max
                                    let left_max = GetMax(*left);
                                    assert(is_max_of_set(left_max, left_vals));
                                    assert(x <= left_max);
                                    assert(max_val >= left_max);
                                    assert(x <= max_val);
                                } else {
                                    // left is empty, so left_vals is empty, contradiction
                                    assert(left_vals =~= Set::empty());
                                    assert(!left_vals.contains(x));
                                    assert(false);
                                }
                            } else if right_vals.contains(x) {
                                if !is_empty(&*right) {
                                    // x is in right subtree, so x <= right_max, and max_val >= right_max
                                    let right_max = GetMax(*right);
                                    assert(is_max_of_set(right_max, right_vals));
                                    assert(x <= right_max);
                                    assert(max_val >= right_max);
                                    assert(x <= max_val);
                                } else {
                                    // right is empty, so right_vals is empty, contradiction
                                    assert(right_vals =~= Set::empty());
                                    assert(!right_vals.contains(x));
                                    assert(false);
                                }
                            } else {
                                // x must be in one of the three categories
                                assert(tree_vals.contains(x));
                                assert(x == value || left_vals.contains(x) || right_vals.contains(x));
                                assert(false);
                            }
                        }
                    }
                };
                
                assert(is_max_of_set(max_val, tree_vals));
            }
            
            max_val
        }
    }
}

fn main() {
    // Example usage
    let tree = Tree::Node {
        value: 5,
        left: Box::new(Tree::Node {
            value: 3,
            left: Box::new(Tree::Leaf),
            right: Box::new(Tree::Leaf),
        }),
        right: Box::new(Tree::Node {
            value: 8,
            left: Box::new(Tree::Leaf),
            right: Box::new(Tree::Leaf),
        }),
    };
    
    let max = GetMax(tree);
    assert(max == 8);
}

}
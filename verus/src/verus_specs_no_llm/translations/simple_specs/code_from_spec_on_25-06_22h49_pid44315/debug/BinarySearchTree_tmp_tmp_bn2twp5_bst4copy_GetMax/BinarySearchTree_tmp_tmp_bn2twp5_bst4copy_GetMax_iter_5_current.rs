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
            
            // Establish that value is in the tree
            proof {
                assert(tree_values(&Tree::Node { value, left, right }).contains(value));
            }
            
            if !is_empty(&*left) {
                let left_max = GetMax(*left);
                proof {
                    assert(is_max_of_set(left_max, tree_values(&*left)));
                    assert(tree_values(&Tree::Node { value, left, right }).contains(left_max));
                }
                if left_max > max_val {
                    max_val = left_max;
                }
            }
            
            if !is_empty(&*right) {
                let right_max = GetMax(*right);
                proof {
                    assert(is_max_of_set(right_max, tree_values(&*right)));
                    assert(tree_values(&Tree::Node { value, left, right }).contains(right_max));
                }
                if right_max > max_val {
                    max_val = right_max;
                }
            }
            
            // Proof that max_val satisfies the postcondition
            proof {
                let tree_vals = tree_values(&Tree::Node { value, left, right });
                
                // Prove that max_val is in the tree
                assert(tree_vals.contains(max_val));
                
                // Prove that max_val is >= all elements
                assert(forall |x: int| tree_vals.contains(x) ==> {
                    // x is either the root value, or in left subtree, or in right subtree
                    if x == value {
                        x <= max_val
                    } else if tree_values(&*left).contains(x) {
                        if !is_empty(&*left) {
                            let left_max = GetMax(*left);
                            x <= left_max && left_max <= max_val
                        } else {
                            false  // contradiction since left is empty
                        }
                    } else if tree_values(&*right).contains(x) {
                        if !is_empty(&*right) {
                            let right_max = GetMax(*right);
                            x <= right_max && right_max <= max_val
                        } else {
                            false  // contradiction since right is empty
                        }
                    } else {
                        false  // x must be somewhere in the tree
                    }
                } ==> x <= max_val);
                
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
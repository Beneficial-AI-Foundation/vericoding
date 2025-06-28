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
            
            // Handle left subtree
            if !is_empty(&*left) {
                let left_max = GetMax(*left);
                proof {
                    assert(is_max_of_set(left_max, tree_values(&*left)));
                }
                if left_max > max_val {
                    max_val = left_max;
                }
            }
            
            // Handle right subtree  
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
                let tree_vals = tree_values(&Tree::Node { value, left: left.clone(), right: right.clone() });
                let left_vals = tree_values(&*left);
                let right_vals = tree_values(&*right);
                
                // Establish that tree_vals is the union
                assert(tree_vals =~= left_vals.union(right_vals).insert(value));
                
                // Prove max_val is in tree_vals
                assert(tree_vals.contains(max_val)) by {
                    if max_val == value {
                        assert(tree_vals.contains(value));
                    } else {
                        // max_val came from a subtree
                        if !is_empty(&*left) {
                            let left_max = GetMax(*left);
                            if max_val == left_max {
                                assert(left_vals.contains(left_max));
                                assert(tree_vals.contains(left_max));
                            }
                        }
                        if !is_empty(&*right) {
                            let right_max = GetMax(*right);
                            if max_val == right_max {
                                assert(right_vals.contains(right_max));
                                assert(tree_vals.contains(right_max));
                            }
                        }
                    }
                };
                
                // Prove max_val >= all elements
                assert(forall |x: int| tree_vals.contains(x) ==> x <= max_val) by {
                    forall |x: int| tree_vals.contains(x) implies x <= max_val {
                        if x == value {
                            assert(x <= max_val);
                        } else if left_vals.contains(x) {
                            if !is_empty(&*left) {
                                let left_max = GetMax(*left);
                                assert(x <= left_max);
                                assert(left_max <= max_val);
                                assert(x <= max_val);
                            } else {
                                assert(left_vals =~= Set::empty());
                                assert(!left_vals.contains(x));
                                assert(false);
                            }
                        } else if right_vals.contains(x) {
                            if !is_empty(&*right) {
                                let right_max = GetMax(*right);
                                assert(x <= right_max);
                                assert(right_max <= max_val);
                                assert(x <= max_val);
                            } else {
                                assert(right_vals =~= Set::empty());
                                assert(!right_vals.contains(x));
                                assert(false);
                            }
                        }
                    }
                };
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
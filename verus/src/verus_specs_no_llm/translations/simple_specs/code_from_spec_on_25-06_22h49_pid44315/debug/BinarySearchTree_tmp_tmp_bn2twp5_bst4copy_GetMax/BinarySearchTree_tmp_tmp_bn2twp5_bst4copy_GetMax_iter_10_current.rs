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
            let left_max_opt = if is_empty(&*left) {
                None
            } else {
                Some(GetMax(*left))
            };
            
            if let Some(left_max) = left_max_opt {
                if left_max > max_val {
                    max_val = left_max;
                }
            }
            
            // Handle right subtree  
            let right_max_opt = if is_empty(&*right) {
                None
            } else {
                Some(GetMax(*right))
            };
            
            if let Some(right_max) = right_max_opt {
                if right_max > max_val {
                    max_val = right_max;
                }
            }
            
            proof {
                let tree_ref = Tree::Node { value, left, right };
                let tree_vals = tree_values(&tree_ref);
                let left_vals = tree_values(&*tree_ref.left);
                let right_vals = tree_values(&*tree_ref.right);
                
                // Establish that tree_vals is the union
                assert(tree_vals =~= left_vals.union(right_vals).insert(value));
                
                // Prove max_val is in tree_vals
                assert(tree_vals.contains(max_val)) by {
                    if max_val == value {
                        assert(tree_vals.contains(value));
                    } else if left_max_opt.is_some() && max_val == left_max_opt.unwrap() {
                        assert(left_vals.contains(max_val));
                        assert(tree_vals.contains(max_val));
                    } else if right_max_opt.is_some() && max_val == right_max_opt.unwrap() {
                        assert(right_vals.contains(max_val));
                        assert(tree_vals.contains(max_val));
                    }
                };
                
                // Prove max_val >= all elements
                assert(forall |x: int| tree_vals.contains(x) ==> x <= max_val) by {
                    forall |x: int| tree_vals.contains(x) implies x <= max_val {
                        if x == value {
                            assert(x <= max_val);
                        } else if left_vals.contains(x) {
                            if left_max_opt.is_some() {
                                let left_max = left_max_opt.unwrap();
                                assert(x <= left_max);
                                assert(left_max <= max_val);
                                assert(x <= max_val);
                            } else {
                                assert(left_vals =~= Set::empty());
                                assert(false);
                            }
                        } else if right_vals.contains(x) {
                            if right_max_opt.is_some() {
                                let right_max = right_max_opt.unwrap();
                                assert(x <= right_max);
                                assert(right_max <= max_val);
                                assert(x <= max_val);
                            } else {
                                assert(right_vals =~= Set::empty());
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
    // Example usage - create tree in exec mode
    let leaf = Tree::Leaf;
    let left_node = Tree::Node {
        value: 3,
        left: Box::new(leaf),
        right: Box::new(Tree::Leaf),
    };
    let right_node = Tree::Node {
        value: 8,
        left: Box::new(Tree::Leaf),
        right: Box::new(Tree::Leaf),
    };
    let tree = Tree::Node {
        value: 5,
        left: Box::new(left_node),
        right: Box::new(right_node),
    };
    
    let max = GetMax(tree);
    assert(max == 8);
}

}
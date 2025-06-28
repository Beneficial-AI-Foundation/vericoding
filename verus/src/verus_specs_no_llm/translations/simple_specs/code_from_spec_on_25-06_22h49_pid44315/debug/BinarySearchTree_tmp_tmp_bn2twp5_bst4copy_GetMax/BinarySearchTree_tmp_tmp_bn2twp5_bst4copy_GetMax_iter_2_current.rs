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
            unreachable!()
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
                let tree_vals = tree_values(&Tree::Node { value, left: left.clone(), right: right.clone() });
                assert(tree_vals.contains(max_val));
                assert(forall |x: int| tree_vals.contains(x) ==> x <= max_val);
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
use builtin::*;
use builtin_macros::*;

verus! {

// Define a binary tree structure
pub enum Tree {
    Leaf,
    Node { value: int, left: Box<Tree>, right: Box<Tree> }
}

impl Tree {
    // Specification function to define the minimum value in a tree
    pub open spec fn min_value(self) -> int 
        decreases self
    {
        match self {
            Tree::Leaf => 0x7fff_ffff_ffff_ffff,  // Use a large value as neutral element
            Tree::Node { value, left, right } => {
                let left_min = left.min_value();
                let right_min = right.min_value();
                
                // Find the minimum among value, left_min, and right_min
                let min_left_right = if left_min <= right_min { left_min } else { right_min };
                if value <= min_left_right { value } else { min_left_right }
            }
        }
    }
    
    // Helper spec function to check if tree is non-empty
    pub open spec fn is_non_empty(self) -> bool {
        match self {
            Tree::Leaf => false,
            Tree::Node { .. } => true,
        }
    }
}

fn GetMin(tree: Tree) -> (res: int)
    requires tree != Tree::Leaf  // Require non-empty tree
    ensures res <= tree.min_value()  // Result is the minimum value
    ensures res == tree.min_value()  // Result is exactly the minimum value
    decreases tree
{
    match tree {
        Tree::Leaf => {
            // This case is unreachable due to precondition
            proof {
                assert(false);  // Contradiction from precondition
            }
            0  // This is unreachable, but we need a concrete value
        }
        Tree::Node { value, left, right } => {
            let mut min_val = value;
            
            // Check left subtree if it exists
            if *left != Tree::Leaf {
                let left_min = GetMin(*left);
                proof {
                    assert(left_min == left.min_value());
                }
                if left_min < min_val {
                    min_val = left_min;
                }
            }
            
            // Check right subtree if it exists  
            if *right != Tree::Leaf {
                let right_min = GetMin(*right);
                proof {
                    assert(right_min == right.min_value());
                }
                if right_min < min_val {
                    min_val = right_min;
                }
            }
            
            // Prove that min_val is indeed the minimum
            proof {
                let large_val = 0x7fff_ffff_ffff_ffff;
                
                // Establish what the spec function computes
                let left_min_spec = if *left == Tree::Leaf { large_val } else { left.min_value() };
                let right_min_spec = if *right == Tree::Leaf { large_val } else { right.min_value() };
                let min_left_right_spec = if left_min_spec <= right_min_spec { left_min_spec } else { right_min_spec };
                let expected_min = if value <= min_left_right_spec { value } else { min_left_right_spec };
                
                assert(tree.min_value() == expected_min);
                
                // Now prove our algorithm computes the same thing
                if *left == Tree::Leaf && *right == Tree::Leaf {
                    // Both subtrees are leaves
                    assert(min_val == value);
                    assert(expected_min == value);
                } else if *left == Tree::Leaf {
                    // Only right subtree exists
                    let right_min = right.min_value();
                    assert(expected_min == if value <= right_min { value } else { right_min });
                    // Our algorithm starts with value, then updates with right_min if smaller
                    assert(min_val == if value <= right_min { value } else { right_min });
                } else if *right == Tree::Leaf {
                    // Only left subtree exists
                    let left_min = left.min_value();
                    assert(expected_min == if value <= left_min { value } else { left_min });
                    // Our algorithm starts with value, then updates with left_min if smaller
                    assert(min_val == if value <= left_min { value } else { left_min });
                } else {
                    // Both subtrees exist
                    let left_min = left.min_value();
                    let right_min = right.min_value();
                    let overall_min = if left_min <= right_min { 
                        if value <= left_min { value } else { left_min }
                    } else {
                        if value <= right_min { value } else { right_min }
                    };
                    assert(expected_min == overall_min);
                    
                    // Our algorithm computes the same by sequentially taking minimums
                    let after_left = if left_min < value { left_min } else { value };
                    let final_min = if right_min < after_left { right_min } else { after_left };
                    assert(min_val == final_min);
                    assert(final_min == overall_min);
                }
                
                assert(min_val == tree.min_value());
            }
            
            min_val
        }
    }
}

fn main() {
}

}
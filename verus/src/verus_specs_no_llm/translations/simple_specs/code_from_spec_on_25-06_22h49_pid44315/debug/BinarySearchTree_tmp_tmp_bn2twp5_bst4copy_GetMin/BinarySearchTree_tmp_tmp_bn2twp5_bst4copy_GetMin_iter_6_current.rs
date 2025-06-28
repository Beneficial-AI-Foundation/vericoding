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
            Tree::Leaf => 2147483647,  // Use a large integer as neutral element
            Tree::Node { value, left, right } => {
                let left_min = left.min_value();
                let right_min = right.min_value();
                
                // Find the minimum among value, left_min, and right_min
                let min_left_right = if left_min <= right_min { left_min } else { right_min };
                if value <= min_left_right { value } else { min_left_right }
            }
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
                assert(false);  // This should be unreachable
            }
            0
        }
        Tree::Node { value, left, right } => {
            let mut min_val = value;
            
            // Check left subtree if it exists
            if *left != Tree::Leaf {
                let left_min = GetMin(*left);
                if left_min < min_val {
                    min_val = left_min;
                }
            }
            
            // Check right subtree if it exists  
            if *right != Tree::Leaf {
                let right_min = GetMin(*right);
                if right_min < min_val {
                    min_val = right_min;
                }
            }
            
            // Proof that min_val is indeed the minimum
            proof {
                let spec_left_min = left.min_value();
                let spec_right_min = right.min_value();
                let spec_min_lr = if spec_left_min <= spec_right_min { spec_left_min } else { spec_right_min };
                let spec_result = if value <= spec_min_lr { value } else { spec_min_lr };
                
                // Prove that min_val equals the specification result
                if *left == Tree::Leaf && *right == Tree::Leaf {
                    // Both subtrees are empty, so min_val should be value
                    assert(min_val == value);
                    assert(spec_left_min == 2147483647);
                    assert(spec_right_min == 2147483647);
                    assert(spec_min_lr == 2147483647);
                    assert(spec_result == value);
                } else if *left == Tree::Leaf {
                    // Only right subtree exists
                    let right_min = GetMin(*right);
                    assert(right_min == spec_right_min);
                    assert(spec_left_min == 2147483647);
                    assert(spec_min_lr == spec_right_min);
                    if right_min < value {
                        assert(min_val == right_min);
                        assert(spec_result == right_min);
                    } else {
                        assert(min_val == value);
                        assert(spec_result == value);
                    }
                } else if *right == Tree::Leaf {
                    // Only left subtree exists
                    let left_min = GetMin(*left);
                    assert(left_min == spec_left_min);
                    assert(spec_right_min == 2147483647);
                    assert(spec_min_lr == spec_left_min);
                    if left_min < value {
                        assert(min_val == left_min);
                        assert(spec_result == left_min);
                    } else {
                        assert(min_val == value);
                        assert(spec_result == value);
                    }
                } else {
                    // Both subtrees exist
                    let left_min = GetMin(*left);
                    let right_min = GetMin(*right);
                    assert(left_min == spec_left_min);
                    assert(right_min == spec_right_min);
                    
                    let actual_min_lr = if left_min <= right_min { left_min } else { right_min };
                    assert(actual_min_lr == spec_min_lr);
                    
                    if actual_min_lr < value {
                        assert(min_val == actual_min_lr);
                        assert(spec_result == actual_min_lr);
                    } else {
                        assert(min_val == value);
                        assert(spec_result == value);
                    }
                }
                
                assert(min_val == spec_result);
                assert(spec_result == tree.min_value());
                assert(min_val == tree.min_value());
            }
            
            min_val
        }
    }
}

fn main() {
}

}
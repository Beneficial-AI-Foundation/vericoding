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
            
            min_val
        }
    }
}

fn main() {
}

}
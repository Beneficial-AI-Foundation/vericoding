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
            Tree::Leaf => int::MAX,  // Use int::MAX as neutral element
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
                assert(tree == Tree::Leaf);
                assert(tree != Tree::Leaf);  // Contradiction from precondition
                assert(false);
            }
            arbitrary()  // This is unreachable
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
                let tree_min = tree.min_value();
                match tree {
                    Tree::Node { value: v, left: l, right: r } => {
                        assert(tree_min == {
                            let left_min = l.min_value();
                            let right_min = r.min_value();
                            let min_left_right = if left_min <= right_min { left_min } else { right_min };
                            if v <= min_left_right { v } else { min_left_right }
                        });
                        
                        // Show that min_val equals tree_min
                        if *l == Tree::Leaf && *r == Tree::Leaf {
                            // Both children are leaves
                            assert(min_val == v);
                            assert(l.min_value() == int::MAX);
                            assert(r.min_value() == int::MAX);
                            assert(tree_min == v);
                        } else if *l == Tree::Leaf {
                            // Only left child is leaf
                            assert(l.min_value() == int::MAX);
                            let right_min = GetMin(*r);
                            assert(right_min == r.min_value());
                            if right_min < v {
                                assert(min_val == right_min);
                                assert(tree_min == right_min);
                            } else {
                                assert(min_val == v);
                                assert(tree_min == v);
                            }
                        } else if *r == Tree::Leaf {
                            // Only right child is leaf
                            assert(r.min_value() == int::MAX);
                            let left_min = GetMin(*l);
                            assert(left_min == l.min_value());
                            if left_min < v {
                                assert(min_val == left_min);
                                assert(tree_min == left_min);
                            } else {
                                assert(min_val == v);
                                assert(tree_min == v);
                            }
                        } else {
                            // Both children are non-leaves
                            let left_min = GetMin(*l);
                            let right_min = GetMin(*r);
                            assert(left_min == l.min_value());
                            assert(right_min == r.min_value());
                            
                            let actual_min = if v <= left_min && v <= right_min {
                                v
                            } else if left_min <= right_min {
                                left_min
                            } else {
                                right_min
                            };
                            assert(min_val == actual_min);
                            assert(tree_min == actual_min);
                        }
                    }
                }
            }
            
            min_val
        }
    }
}

fn main() {
}

}
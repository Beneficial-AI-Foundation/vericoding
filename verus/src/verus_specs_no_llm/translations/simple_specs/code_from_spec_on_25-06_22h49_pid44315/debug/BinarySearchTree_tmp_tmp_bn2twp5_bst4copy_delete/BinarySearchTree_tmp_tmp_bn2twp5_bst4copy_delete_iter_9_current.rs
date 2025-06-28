use builtin::*;
use builtin_macros::*;

verus! {

// Define the Tree enum
#[derive(PartialEq, Eq)]
enum Tree {
    Empty,
    Node(Box<Tree>, int, Box<Tree>),
}

impl Tree {
    spec fn left(self) -> Tree {
        match self {
            Tree::Empty => Tree::Empty,
            Tree::Node(l, _, _) => *l,
        }
    }
    
    spec fn right(self) -> Tree {
        match self {
            Tree::Empty => Tree::Empty,
            Tree::Node(_, _, r) => *r,
        }
    }
    
    spec fn value(self) -> int {
        match self {
            Tree::Empty => 0, // arbitrary value for Empty case
            Tree::Node(_, v, _) => v,
        }
    }
    
    spec fn height(self) -> nat 
        decreases self
    {
        match self {
            Tree::Empty => 0,
            Tree::Node(left, _, right) => {
                1 + if left.height() > right.height() { left.height() } else { right.height() }
            }
        }
    }
}

spec fn all_values_less_than(tree: Tree, max: int) -> bool 
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            v < max && all_values_less_than(*left, max) && all_values_less_than(*right, max)
        }
    }
}

spec fn all_values_greater_than(tree: Tree, min: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            v > min && all_values_greater_than(*left, min) && all_values_greater_than(*right, min)
        }
    }
}

spec fn BinarySearchTree(tree: Tree) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, value, right) => {
            all_values_less_than(*left, value)
            && all_values_greater_than(*right, value)
            && BinarySearchTree(*left) 
            && BinarySearchTree(*right)
        }
    }
}

spec fn minValue(tree: Tree, min: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            (min <= v) && minValue(*left, min) && minValue(*right, min)
        }
    }
}

spec fn maxValue(tree: Tree, max: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            (max >= v) && maxValue(*left, max) && maxValue(*right, max)
        }
    }
}

spec fn contains_value(tree: Tree, val: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => false,
        Tree::Node(left, v, right) => {
            v == val || contains_value(*left, val) || contains_value(*right, val)
        }
    }
}

// Helper proof function to establish BST properties
proof fn lemma_bst_subtrees(tree: Tree)
    requires BinarySearchTree(tree)
    ensures match tree {
        Tree::Empty => true,
        Tree::Node(left, value, right) => {
            BinarySearchTree(*left) && BinarySearchTree(*right) &&
            all_values_less_than(*left, value) && all_values_greater_than(*right, value)
        }
    }
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, value, right) => {
            lemma_bst_subtrees(*left);
            lemma_bst_subtrees(*right);
        }
    }
}

// Lemma: if tree is BST and contains value v, then all values in left are < v and all in right are > v
proof fn lemma_bst_bounds(tree: Tree, v: int)
    requires BinarySearchTree(tree), contains_value(tree, v)
    ensures match tree {
        Tree::Empty => false,
        Tree::Node(left, value, right) => {
            if value == v {
                all_values_less_than(*left, v) && all_values_greater_than(*right, v)
            } else {
                true
            }
        }
    }
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, value, right) => {
            if value == v {
                lemma_bst_subtrees(tree);
            }
        }
    }
}

// Lemma: BST property is preserved when combining subtrees with appropriate root
proof fn lemma_bst_construction(left: Tree, root: int, right: Tree)
    requires BinarySearchTree(left), 
             BinarySearchTree(right),
             all_values_less_than(left, root),
             all_values_greater_than(right, root)
    ensures BinarySearchTree(Tree::Node(Box::new(left), root, Box::new(right)))
{
    // This follows directly from the definition of BinarySearchTree
}

// Lemma about minimum value properties
proof fn lemma_min_properties(tree: Tree, min_val: int)
    requires tree != Tree::Empty,
             BinarySearchTree(tree),
             contains_value(tree, min_val),
             forall |x: int| contains_value(tree, x) ==> min_val <= x
    ensures all_values_greater_than(tree, min_val - 1)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, value, right) => {
            if *left != Tree::Empty {
                lemma_min_properties(*left, min_val);
            }
            if *right != Tree::Empty {
                lemma_min_properties(*right, min_val);
            }
        }
    }
}

fn GetMin(tree: Tree) -> (res: int)
    requires tree != Tree::Empty,
             BinarySearchTree(tree)
    ensures BinarySearchTree(tree), // tree unchanged
            forall |x: int| contains_value(tree, x) ==> res <= x,
            contains_value(tree, res)
    decreases tree.height()
{
    match tree {
        Tree::Empty => 0, // This case won't be reached due to precondition
        Tree::Node(left, value, right) => {
            if *left == Tree::Empty {
                value
            } else {
                proof {
                    lemma_bst_subtrees(tree);
                }
                GetMin(*left)
            }
        }
    }
}

fn delete(tree: Tree, value: int) -> (res: Tree)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(res)
    decreases tree.height()
{
    match tree {
        Tree::Empty => Tree::Empty,
        Tree::Node(left, v, right) => {
            proof {
                lemma_bst_subtrees(tree);
            }
            
            if value < v {
                let new_left = delete(*left, value);
                proof {
                    lemma_bst_construction(new_left, v, *right);
                }
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
                let new_right = delete(*right, value);
                proof {
                    lemma_bst_construction(*left, v, new_right);
                }
                Tree::Node(left, v, Box::new(new_right))
            } else {
                // Found the node to delete
                if *left == Tree::Empty {
                    *right
                } else if *right == Tree::Empty {
                    *left
                } else {
                    // Node has two children - replace with minimum from right subtree
                    let min_right = GetMin(*right);
                    let new_right = delete(*right, min_right);
                    
                    proof {
                        // Establish that min_right maintains BST properties
                        lemma_bst_subtrees(tree);
                        
                        // min_right is the minimum of right subtree, so it's > all values in left
                        assert(forall |x: int| contains_value(*right, x) ==> min_right <= x);
                        assert(contains_value(*right, min_right));
                        assert(all_values_greater_than(*right, v));
                        assert(min_right > v);
                        assert(all_values_less_than(*left, v));
                        assert(all_values_less_than(*left, min_right));
                        
                        // After deleting min_right from right subtree, remaining values are still > min_right
                        // This requires understanding that delete preserves BST and bounds
                        lemma_bst_construction(*left, min_right, new_right);
                    }
                    
                    Tree::Node(left, min_right, Box::new(new_right))
                }
            }
        }
    }
}

fn main() {
    // Example usage
    let tree = Tree::Node(
        Box::new(Tree::Node(Box::new(Tree::Empty), 1, Box::new(Tree::Empty))),
        2,
        Box::new(Tree::Node(Box::new(Tree::Empty), 3, Box::new(Tree::Empty)))
    );
    
    let result = delete(tree, 2);
    // Tree after deletion
}

}
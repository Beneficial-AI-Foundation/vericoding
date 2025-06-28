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

proof fn lemma_all_values_transitive(tree: Tree, x: int, y: int)
    requires all_values_greater_than(tree, x), x >= y
    ensures all_values_greater_than(tree, y)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            lemma_all_values_transitive(*left, x, y);
            lemma_all_values_transitive(*right, x, y);
        }
    }
}

proof fn lemma_all_values_less_transitive(tree: Tree, x: int, y: int)
    requires all_values_less_than(tree, x), x <= y
    ensures all_values_less_than(tree, y)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            lemma_all_values_less_transitive(*left, x, y);
            lemma_all_values_less_transitive(*right, x, y);
        }
    }
}

proof fn lemma_getmin_is_minimum(tree: Tree, min_val: int)
    requires tree != Tree::Empty, BinarySearchTree(tree)
    ensures {
        let min = GetMin(tree);
        contains_value(tree, min) && 
        (forall |x: int| contains_value(tree, x) ==> min <= x)
    }
    decreases tree.height()
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, value, right) => {
            lemma_bst_subtrees(tree);
            if *left == Tree::Empty {
                assert(contains_value(tree, value));
                assert(all_values_greater_than(*right, value));
            } else {
                lemma_getmin_is_minimum(*left, min_val);
            }
        }
    }
}

proof fn lemma_delete_preserves_bounds(tree: Tree, del_val: int, lower: int, upper: int)
    requires BinarySearchTree(tree),
             all_values_greater_than(tree, lower),
             all_values_less_than(tree, upper)
    ensures {
        let result = delete(tree, del_val);
        BinarySearchTree(result) &&
        all_values_greater_than(result, lower) &&
        all_values_less_than(result, upper)
    }
    decreases tree.height()
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            lemma_bst_subtrees(tree);
            if del_val < v {
                lemma_delete_preserves_bounds(*left, del_val, lower, v);
            } else if del_val > v {
                lemma_delete_preserves_bounds(*right, del_val, v, upper);
            } else {
                if *right != Tree::Empty {
                    lemma_getmin_is_minimum(*right, v);
                    let min_right = GetMin(*right);
                    lemma_delete_preserves_bounds(*right, min_right, v, upper);
                }
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
                proof {
                    lemma_bst_subtrees(tree);
                    assert(all_values_greater_than(*right, value));
                }
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
                    lemma_delete_preserves_bounds(*left, value, int::MIN, v);
                    lemma_bst_construction(new_left, v, *right);
                }
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
                let new_right = delete(*right, value);
                proof {
                    lemma_delete_preserves_bounds(*right, value, v, int::MAX);
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
                        lemma_bst_subtrees(tree);
                        lemma_getmin_is_minimum(*right, v);
                        lemma_delete_preserves_bounds(*right, min_right, v, int::MAX);
                        
                        // min_right is minimum of right subtree, so min_right > v (since all right values > v)
                        // and all left values < v < min_right
                        lemma_all_values_transitive(*left, v, min_right);
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
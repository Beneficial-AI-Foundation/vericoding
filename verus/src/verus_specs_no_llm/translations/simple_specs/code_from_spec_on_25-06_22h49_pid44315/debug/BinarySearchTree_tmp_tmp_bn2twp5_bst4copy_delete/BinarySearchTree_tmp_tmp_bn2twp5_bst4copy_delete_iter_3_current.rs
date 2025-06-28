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
    
    spec fn height(self) -> nat {
        match self {
            Tree::Empty => 0,
            Tree::Node(left, _, right) => {
                1 + if left.height() > right.height() { left.height() } else { right.height() }
            }
        }
    }
}

spec fn all_values_less_than(tree: Tree, max: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            v < max && all_values_less_than(*left, max) && all_values_less_than(*right, max)
        }
    }
}

spec fn all_values_greater_than(tree: Tree, min: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            v > min && all_values_greater_than(*left, min) && all_values_greater_than(*right, min)
        }
    }
}

spec fn BinarySearchTree(tree: Tree) -> bool {
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

spec fn minValue(tree: Tree, min: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            (min <= v) && minValue(*left, min) && minValue(*right, min)
        }
    }
}

spec fn maxValue(tree: Tree, max: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            (max >= v) && maxValue(*left, max) && maxValue(*right, max)
        }
    }
}

// Helper lemma to establish that GetMin returns the actual minimum
proof fn lemma_get_min_is_minimum(tree: Tree, min_val: int)
    requires tree != Tree::Empty,
             BinarySearchTree(tree),
             min_val == GetMin(tree)
    ensures forall |x: int| contains_value(tree, x) ==> min_val <= x
    decreases tree.height()
{
    match tree {
        Tree::Node(left, value, right) => {
            if *left == Tree::Empty {
                // min_val == value, and all values in right are > value
                // so min_val is indeed minimum
            } else {
                lemma_get_min_is_minimum(*left, min_val);
                // Since BST property holds, all values in right subtree > value
                // and all values in left subtree < value
                // GetMin returns minimum of left subtree which is <= value
            }
        }
        Tree::Empty => {}
    }
}

spec fn contains_value(tree: Tree, val: int) -> bool {
    match tree {
        Tree::Empty => false,
        Tree::Node(left, v, right) => {
            v == val || contains_value(*left, val) || contains_value(*right, val)
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
                    // In BST, if left is empty, then value is minimum
                    // All values in right are > value due to BST property
                }
                value
            } else {
                proof {
                    // GetMin(*left) will return minimum of left subtree
                    // Due to BST property, all values in left < value
                    // So minimum of left is minimum of entire tree
                }
                GetMin(*left)
            }
        }
    }
}

// Helper lemma for delete verification
proof fn lemma_delete_preserves_bst_structure(tree: Tree, value: int, result: Tree)
    requires BinarySearchTree(tree),
             result == delete(tree, value)
    ensures BinarySearchTree(result)
    decreases tree.height()
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_delete_preserves_bst_structure(*left, value, delete(*left, value));
            } else if value > v {
                lemma_delete_preserves_bst_structure(*right, value, delete(*right, value));
            } else {
                if *left != Tree::Empty && *right != Tree::Empty {
                    let min_right = GetMin(*right);
                    // Need to show that replacing v with min_right preserves BST
                    // min_right is minimum of right subtree, so it's > all values in left
                    // and <= all values in right subtree
                }
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
            if value < v {
                let new_left = delete(*left, value);
                proof {
                    // Recursively deleting from left preserves BST property of left subtree
                    // Combined with unchanged right subtree, overall BST property preserved
                }
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
                let new_right = delete(*right, value);
                proof {
                    // Recursively deleting from right preserves BST property of right subtree
                    // Combined with unchanged left subtree, overall BST property preserved
                }
                Tree::Node(left, v, Box::new(new_right))
            } else {
                // Found the node to delete
                if *left == Tree::Empty {
                    proof {
                        // Right subtree maintains BST property
                    }
                    *right
                } else if *right == Tree::Empty {
                    proof {
                        // Left subtree maintains BST property
                    }
                    *left
                } else {
                    // Node has two children - replace with minimum from right subtree
                    let min_right = GetMin(*right);
                    let new_right = delete(*right, min_right);
                    proof {
                        // min_right is minimum of right subtree
                        // So min_right > all values in left subtree (BST property)
                        // After removing min_right from right subtree, remaining values
                        // are still > min_right, so BST property preserved
                        assert(all_values_less_than(*left, min_right));
                        assert(all_values_greater_than(new_right, min_right));
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
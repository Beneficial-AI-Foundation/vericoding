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

spec fn contains_value(tree: Tree, val: int) -> bool {
    match tree {
        Tree::Empty => false,
        Tree::Node(left, v, right) => {
            v == val || contains_value(*left, val) || contains_value(*right, val)
        }
    }
}

// Helper lemma: if all values in tree are less than max, and we delete a value, property is preserved
proof fn lemma_delete_preserves_less_than(tree: Tree, value: int, max: int)
    requires BinarySearchTree(tree), all_values_less_than(tree, max)
    ensures all_values_less_than(delete(tree, value), max)
    decreases tree.height()
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_delete_preserves_less_than(*left, value, max);
            } else if value > v {
                lemma_delete_preserves_less_than(*right, value, max);
            } else {
                if *left != Tree::Empty && *right != Tree::Empty {
                    let min_right = GetMin(*right);
                    lemma_delete_preserves_less_than(*right, min_right, max);
                }
            }
        }
    }
}

// Helper lemma: if all values in tree are greater than min, and we delete a value, property is preserved
proof fn lemma_delete_preserves_greater_than(tree: Tree, value: int, min: int)
    requires BinarySearchTree(tree), all_values_greater_than(tree, min)
    ensures all_values_greater_than(delete(tree, value), min)
    decreases tree.height()
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_delete_preserves_greater_than(*left, value, min);
            } else if value > v {
                lemma_delete_preserves_greater_than(*right, value, min);
            } else {
                if *left != Tree::Empty && *right != Tree::Empty {
                    let min_right = GetMin(*right);
                    lemma_delete_preserves_greater_than(*right, min_right, min);
                }
            }
        }
    }
}

// Lemma: BST property implies all values greater than left subtree
proof fn lemma_bst_left_less_than_root(tree: Tree)
    requires BinarySearchTree(tree), tree != Tree::Empty
    ensures all_values_less_than(tree.left(), tree.value())
{
    match tree {
        Tree::Node(left, value, right) => {
            assert(all_values_less_than(*left, value));
        }
        Tree::Empty => {}
    }
}

// Lemma: BST property implies all values in right subtree greater than root
proof fn lemma_bst_right_greater_than_root(tree: Tree)
    requires BinarySearchTree(tree), tree != Tree::Empty
    ensures all_values_greater_than(tree.right(), tree.value())
{
    match tree {
        Tree::Node(left, value, right) => {
            assert(all_values_greater_than(*right, value));
        }
        Tree::Empty => {}
    }
}

// Lemma: GetMin returns a value that exists in the tree
proof fn lemma_get_min_exists(tree: Tree)
    requires tree != Tree::Empty, BinarySearchTree(tree)
    ensures contains_value(tree, GetMin(tree))
    decreases tree.height()
{
    match tree {
        Tree::Node(left, value, right) => {
            if *left == Tree::Empty {
                assert(contains_value(tree, value));
            } else {
                lemma_get_min_exists(*left);
                assert(contains_value(*left, GetMin(*left)));
                assert(contains_value(tree, GetMin(*left)));
            }
        }
        Tree::Empty => {}
    }
}

// Lemma: GetMin returns the minimum value
proof fn lemma_get_min_is_minimum(tree: Tree)
    requires tree != Tree::Empty, BinarySearchTree(tree)
    ensures forall |x: int| contains_value(tree, x) ==> GetMin(tree) <= x
    decreases tree.height()
{
    match tree {
        Tree::Node(left, value, right) => {
            if *left == Tree::Empty {
                // value is the minimum since all right values are > value
                assert(forall |x: int| contains_value(*right, x) ==> value < x);
            } else {
                lemma_get_min_is_minimum(*left);
                let min_left = GetMin(*left);
                assert(forall |x: int| contains_value(*left, x) ==> min_left <= x);
                // min_left < value due to BST property
                assert(all_values_less_than(*left, value));
                assert(min_left < value);
                // All values in right > value > min_left
                assert(forall |x: int| contains_value(*right, x) ==> min_left < x);
            }
        }
        Tree::Empty => {}
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
    proof { lemma_get_min_exists(tree); }
    proof { lemma_get_min_is_minimum(tree); }
    
    match tree {
        Tree::Empty => 0, // This case won't be reached due to precondition
        Tree::Node(left, value, right) => {
            if *left == Tree::Empty {
                value
            } else {
                GetMin(*left)
            }
        }
    }
}

// Lemma: Deleting from subtree preserves BST when combined properly
proof fn lemma_delete_left_preserves_bst(tree: Tree, value: int)
    requires BinarySearchTree(tree),
             tree != Tree::Empty,
             value < tree.value()
    ensures BinarySearchTree(Tree::Node(Box::new(delete(tree.left(), value)), tree.value(), Box::new(tree.right())))
    decreases tree.height()
{
    match tree {
        Tree::Node(left, v, right) => {
            let new_left = delete(*left, value);
            assert(BinarySearchTree(new_left));
            lemma_delete_preserves_less_than(*left, value, v);
            assert(all_values_less_than(new_left, v));
            assert(all_values_greater_than(*right, v));
        }
        Tree::Empty => {}
    }
}

proof fn lemma_delete_right_preserves_bst(tree: Tree, value: int)
    requires BinarySearchTree(tree),
             tree != Tree::Empty,
             value > tree.value()
    ensures BinarySearchTree(Tree::Node(Box::new(tree.left()), tree.value(), Box::new(delete(tree.right(), value))))
    decreases tree.height()
{
    match tree {
        Tree::Node(left, v, right) => {
            let new_right = delete(*right, value);
            assert(BinarySearchTree(new_right));
            assert(all_values_less_than(*left, v));
            lemma_delete_preserves_greater_than(*right, value, v);
            assert(all_values_greater_than(new_right, v));
        }
        Tree::Empty => {}
    }
}

// Lemma: Min of right subtree is greater than all values in left subtree
proof fn lemma_min_right_greater_than_left(left: Tree, right: Tree, root_val: int)
    requires BinarySearchTree(Tree::Node(Box::new(left), root_val, Box::new(right))),
             right != Tree::Empty
    ensures all_values_less_than(left, GetMin(right))
{
    let min_right = GetMin(right);
    assert(all_values_less_than(left, root_val));
    assert(all_values_greater_than(right, root_val));
    lemma_get_min_exists(right);
    assert(contains_value(right, min_right));
    assert(min_right > root_val);
    assert(forall |x: int| contains_value(left, x) ==> x < root_val < min_right);
}

fn delete(tree: Tree) -> (res: Tree)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(res)
    decreases tree.height()
{
    match tree {
        Tree::Empty => Tree::Empty,
        Tree::Node(left, v, right) => {
            if value < v {
                proof { lemma_delete_left_preserves_bst(tree, value); }
                let new_left = delete(*left, value);
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
                proof { lemma_delete_right_preserves_bst(tree, value); }
                let new_right = delete(*right, value);
                Tree::Node(left, v, Box::new(new_right))
            } else {
                // Found the node to delete
                if *left == Tree::Empty {
                    *right
                } else if *right == Tree::Empty {
                    *left
                } else {
                    // Node has two children - replace with minimum from right subtree
                    proof { lemma_min_right_greater_than_left(*left, *right, v); }
                    let min_right = GetMin(*right);
                    let new_right = delete(*right, min_right);
                    proof {
                        assert(all_values_less_than(*left, min_right));
                        lemma_delete_preserves_greater_than(*right, min_right, min_right);
                        assert(all_values_greater_than(new_right, min_right));
                        assert(BinarySearchTree(*left));
                        assert(BinarySearchTree(new_right));
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
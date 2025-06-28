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
            if value < v {
                let new_left = delete(*left, value);
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
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
                    let min_right = GetMin(*right);
                    let new_right = delete(*right, min_right);
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
use builtin::*;
use builtin_macros::*;

verus! {

// Define the Tree enum
enum Tree {
    Empty,
    Node(Box<Tree>, int, Box<Tree>),
}

fn main() {
}

// Helper functions for cleaner code
spec fn is_empty(tree: Tree) -> bool {
    matches!(tree, Tree::Empty)
}

spec fn get_value(tree: Tree) -> int 
    requires !is_empty(tree)
{
    match tree {
        Tree::Node(_, v, _) => v,
        Tree::Empty => arbitrary(), // unreachable due to precondition
    }
}

spec fn get_left(tree: Tree) -> Tree
    requires !is_empty(tree)
{
    match tree {
        Tree::Node(left, _, _) => *left,
        Tree::Empty => arbitrary(), // unreachable due to precondition
    }
}

spec fn get_right(tree: Tree) -> Tree
    requires !is_empty(tree)
{
    match tree {
        Tree::Node(_, _, right) => *right,
        Tree::Empty => arbitrary(), // unreachable due to precondition
    }
}

spec fn all_less_than(tree: Tree, max: int) -> bool 
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            v < max && all_less_than(*left, max) && all_less_than(*right, max)
        }
    }
}

spec fn all_greater_than(tree: Tree, min: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            v > min && all_greater_than(*left, min) && all_greater_than(*right, min)
        }
    }
}

spec fn BinarySearchTree(tree: Tree) -> bool 
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, value, right) => {
            all_less_than(*left, value)
            && all_greater_than(*right, value)
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
        Tree::Node(left, v, right) => (min < v) && minValue(*left, min) && minValue(*right, min)
    }
}

spec fn maxValue(tree: Tree, max: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => (max > v) && maxValue(*left, max) && maxValue(*right, max)
    }
}

// Lemma to help with verification
proof fn lemma_bst_implies_bounds(tree: Tree, min: int, max: int)
    requires BinarySearchTree(tree)
    ensures minValue(tree, min) <==> all_greater_than(tree, min)
    ensures maxValue(tree, max) <==> all_less_than(tree, max)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            lemma_bst_implies_bounds(*left, min, max);
            lemma_bst_implies_bounds(*right, min, max);
        }
    }
}

proof fn lemma_insert_preserves_bounds(tree: Tree, value: int, min: int, max: int)
    requires BinarySearchTree(tree)
    ensures 
        min < value ==> (all_greater_than(tree, min) ==> all_greater_than(insert_result(tree, value), min)),
        max > value ==> (all_less_than(tree, max) ==> all_less_than(insert_result(tree, value), max))
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_insert_preserves_bounds(*left, value, min, max);
            } else if value > v {
                lemma_insert_preserves_bounds(*right, value, min, max);
            }
        }
    }
}

spec fn insert_result(tree: Tree, value: int) -> Tree {
    match tree {
        Tree::Empty => Tree::Node(Box::new(Tree::Empty), value, Box::new(Tree::Empty)),
        Tree::Node(left, v, right) => {
            if value < v {
                Tree::Node(Box::new(insert_result(*left, value)), v, right)
            } else if value > v {
                Tree::Node(left, v, Box::new(insert_result(*right, value)))
            } else {
                tree
            }
        }
    }
}

fn insertRecursion(tree: Tree, value: int) -> (res: Tree)
    requires
        BinarySearchTree(tree)
    ensures
        res != Tree::Empty,
        BinarySearchTree(res),
        forall|x: int| minValue(tree, x) && x < value ==> minValue(res, x),
        forall|x: int| maxValue(tree, x) && x > value ==> maxValue(res, x),
        res == insert_result(tree, value)
    decreases tree
{
    proof {
        lemma_bst_implies_bounds(tree, value - 1, value + 1);
    }
    
    match tree {
        Tree::Empty => {
            Tree::Node(Box::new(Tree::Empty), value, Box::new(Tree::Empty))
        },
        Tree::Node(left, v, right) => {
            if value < v {
                let new_left = insertRecursion(*left, value);
                proof {
                    lemma_insert_preserves_bounds(*left, value, value - 1, v);
                }
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
                let new_right = insertRecursion(*right, value);
                proof {
                    lemma_insert_preserves_bounds(*right, value, v, value + 1);
                }
                Tree::Node(left, v, Box::new(new_right))
            } else {
                // value == v, don't insert duplicates
                tree
            }
        }
    }
}

}
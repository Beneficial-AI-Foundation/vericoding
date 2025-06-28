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

spec fn insert_result(tree: Tree, value: int) -> Tree 
    decreases tree
{
    match tree {
        Tree::Empty => Tree::Node(box Tree::Empty, value, box Tree::Empty),
        Tree::Node(left, v, right) => {
            if value < v {
                Tree::Node(box insert_result(*left, value), v, right)
            } else if value > v {
                Tree::Node(left, v, box insert_result(*right, value))
            } else {
                tree
            }
        }
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

proof fn lemma_insert_result_bst(tree: Tree, value: int)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(insert_result(tree, value))
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_insert_result_bst(*left, value);
                // Prove that insert_result(*left, value) maintains the BST property
                assert(all_less_than(insert_result(*left, value), v));
            } else if value > v {
                lemma_insert_result_bst(*right, value);
                // Prove that insert_result(*right, value) maintains the BST property
                assert(all_greater_than(insert_result(*right, value), v));
            }
        }
    }
}

proof fn lemma_insert_min_value(tree: Tree, value: int, x: int)
    requires BinarySearchTree(tree), minValue(tree, x), x < value
    ensures minValue(insert_result(tree, value), x)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_insert_min_value(*left, value, x);
            } else if value > v {
                lemma_insert_min_value(*right, value, x);
            }
        }
    }
}

proof fn lemma_insert_max_value(tree: Tree, value: int, x: int)
    requires BinarySearchTree(tree), maxValue(tree, x), x > value
    ensures maxValue(insert_result(tree, value), x)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_insert_max_value(*left, value, x);
            } else if value > v {
                lemma_insert_max_value(*right, value, x);
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
        lemma_insert_result_bst(tree, value);
        
        // Prove the minValue and maxValue properties
        assert forall|x: int| minValue(tree, x) && x < value implies minValue(insert_result(tree, value), x) by {
            lemma_insert_min_value(tree, value, x);
        };
        
        assert forall|x: int| maxValue(tree, x) && x > value implies maxValue(insert_result(tree, value), x) by {
            lemma_insert_max_value(tree, value, x);
        };
    }
    
    match tree {
        Tree::Empty => {
            Tree::Node(box Tree::Empty, value, box Tree::Empty)
        },
        Tree::Node(left, v, right) => {
            if value < v {
                let new_left = insertRecursion(*left, value);
                proof {
                    lemma_insert_preserves_bounds(*left, value, value - 1, v);
                }
                Tree::Node(box new_left, v, right)
            } else if value > v {
                let new_right = insertRecursion(*right, value);
                proof {
                    lemma_insert_preserves_bounds(*right, value, v, value + 1);
                }
                Tree::Node(left, v, box new_right)
            } else {
                // value == v, don't insert duplicates
                tree
            }
        }
    }
}

}
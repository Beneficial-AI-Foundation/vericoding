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

// Helper lemmas for bounds preservation
proof fn lemma_all_less_than_preserves(tree: Tree, max: int, value: int)
    requires 
        all_less_than(tree, max),
        value < max
    ensures all_less_than(insert_result(tree, value), max)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_all_less_than_preserves(*left, max, value);
            } else if value > v {
                lemma_all_less_than_preserves(*right, max, value);
            }
        }
    }
}

proof fn lemma_all_greater_than_preserves(tree: Tree, min: int, value: int)
    requires 
        all_greater_than(tree, min),
        value > min
    ensures all_greater_than(insert_result(tree, value), min)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_all_greater_than_preserves(*left, min, value);
            } else if value > v {
                lemma_all_greater_than_preserves(*right, min, value);
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
                lemma_all_less_than_preserves(*left, v, value);
            } else if value > v {
                lemma_insert_result_bst(*right, value);
                lemma_all_greater_than_preserves(*right, v, value);
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

proof fn lemma_insert_not_empty(tree: Tree, value: int)
    ensures insert_result(tree, value) != Tree::Empty
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_insert_not_empty(*left, value);
            } else if value > v {
                lemma_insert_not_empty(*right, value);
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
        lemma_insert_result_bst(tree, value);
        lemma_insert_not_empty(tree, value);
    }
    
    match tree {
        Tree::Empty => {
            Tree::Node(Box::new(Tree::Empty), value, Box::new(Tree::Empty))
        },
        Tree::Node(left, v, right) => {
            if value < v {
                let new_left = insertRecursion(*left, value);
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
                let new_right = insertRecursion(*right, value);
                Tree::Node(left, v, Box::new(new_right))
            } else {
                // value == v, don't insert duplicates
                tree
            }
        }
    }
}

}
use vstd::prelude::*;

verus! {

pub enum Tree {
    Empty,
    Node { left: Box<Tree>, value: int, right: Box<Tree> },
}

pub open spec fn binary_search_tree(tree: Tree) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value, right } => {
            (left.is_Empty() || left.get_Node_value() < value)
            && (right.is_Empty() || right.get_Node_value() > value)
            && binary_search_tree(*left) && binary_search_tree(*right)
            && min_value(*right, value) && max_value(*left, value)
        }
    }
}

pub open spec fn max_value(tree: Tree, max: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => {
            (max > v) && max_value(*left, max) && max_value(*right, max)
        }
    }
}

pub open spec fn min_value(tree: Tree, min: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => {
            (min < v) && min_value(*left, min) && min_value(*right, min)
        }
    }
}

impl Tree {
    pub open spec fn is_Empty(&self) -> bool {
        matches!(*self, Tree::Empty)
    }

    pub open spec fn get_Node_value(&self) -> int {
        match self {
            Tree::Node { value, .. } => *value,
            _ => arbitrary(),
        }
    }
}

// <vc-helpers>
spec fn min_value_recursive(tree: Tree, min: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => {
            min < v && min_value_recursive(*left, min) && min_value_recursive(*right, min)
        }
    }
}

spec fn max_value_recursive(tree: Tree, max: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => {
            max > v && max_value_recursive(*left, max) && max_value_recursive(*right, max)
        }
    }
}

proof fn min_value_implies_recursive(tree: Tree, min: int)
    requires min_value(tree, min)
    ensures min_value_recursive(tree, min)
    decreases tree
{
    match tree {
        Tree::Empty => (),
        Tree::Node { left, value: v, right } => {
            min_value_implies_recursive(*left, min);
            min_value_implies_recursive(*right, min);
        }
    }
}

proof fn max_value_implies_recursive(tree: Tree, max: int)
    requires max_value(tree, max)
    ensures max_value_recursive(tree, max)
    decreases tree
{
    match tree {
        Tree::Empty => (),
        Tree::Node { left, value: v, right } => {
            max_value_implies_recursive(*left, max);
            max_value_implies_recursive(*right, max);
        }
    }
}

proof fn binary_search_tree_properties(tree: Tree)
    requires binary_search_tree(tree)
    ensures
        match tree {
            Tree::Empty => true,
            Tree::Node { left, value, right } => {
                binary_search_tree(*left) && binary_search_tree(*right) &&
                (left.is_Empty() || max_value_recursive(*left, value)) &&
                (right.is_Empty() || min_value_recursive(*right, value))
            }
        }
    decreases tree
{
    match tree {
        Tree::Empty => (),
        Tree::Node { left, value, right } => {
            binary_search_tree_properties(*left);
            binary_search_tree_properties(*right);
            if !left.is_Empty() {
                max_value_implies_recursive(*left, value);
            }
            if !right.is_Empty() {
                min_value_implies_recursive(*right, value);
            }
        }
    }
}

proof fn insert_preserves_min_value(tree: Tree, value: int, x: int)
    requires 
        binary_search_tree(tree),
        min_value(tree, x),
        x < value
    ensures 
        min_value(insert_recursion(tree, value), x)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: v, right } => {
            if value < v {
                insert_preserves_min_value(*left, value, x);
            } else if value > v {
                insert_preserves_min_value(*right, value, x);
            } else {}
        }
    }
}

proof fn insert_preserves_max_value(tree: Tree, value: int, x: int)
    requires 
        binary_search_tree(tree),
        max_value(tree, x),
        x > value
    ensures 
        max_value(insert_recursion(tree, value), x)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: v, right } => {
            if value < v {
                insert_preserves_max_value(*left, value, x);
            } else if value > v {
                insert_preserves_max_value(*right, value, x);
            } else {}
        }
    }
}

proof fn insert_maintains_min_value_relation(tree: Tree, value: int, min_val: int)
    requires 
        binary_search_tree(tree),
        min_value(tree, min_val),
        min_val < value
    ensures 
        min_value(insert_recursion(tree, value), min_val)
    decreases tree
{
    insert_preserves_min_value(tree, value, min_val);
}

proof fn insert_maintains_max_value_relation(tree: Tree, value: int, max_val: int)
    requires 
        binary_search_tree(tree),
        max_value(tree, max_val),
        max_val > value
    ensures 
        max_value(insert_recursion(tree, value), max_val)
    decreases tree
{
    insert_preserves_max_value(tree, value, max_val);
}

proof fn insert_maintains_bst(tree: Tree, value: int)
    requires binary_search_tree(tree)
    ensures binary_search_tree(insert_recursion(tree, value))
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: v, right } => {
            if value < v {
                insert_maintains_bst(*left, value);
                binary_search_tree_properties(*left);
                if !left.is_Empty() {
                    max_value_implies_recursive(*left, v);
                }
            } else if value > v {
                insert_maintains_bst(*right, value);
                binary_search_tree_properties(*right);
                if !right.is_Empty() {
                    min_value_implies_recursive(*right, v);
                }
            } else {}
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn insert_recursion(tree: Tree, value: int) -> (res: Tree)
    requires binary_search_tree(tree),
    decreases tree,
    ensures res != Tree::Empty ==> binary_search_tree(res),
    ensures forall|x: int| min_value(tree, x) && x < value ==> min_value(res, x),
    ensures forall|x: int| max_value(tree, x) && x > value ==> max_value(res, x),
// </vc-spec>
// <vc-code>
{
    match tree {
        Tree::Empty => {
            Tree::Node {
                left: Box::new(Tree::Empty),
                value,
                right: Box::new(Tree::Empty),
            }
        }
        Tree::Node { left, value: v, right } => {
            if value < v {
                let new_left = insert_recursion(*left, value);
                proof {
                    insert_maintains_bst(*left, value);
                }
                Tree::Node {
                    left: Box::new(new_left),
                    value: v,
                    right,
                }
            } else if value > v {
                let new_right = insert_recursion(*right, value);
                proof {
                    insert_maintains_bst(*right, value);
                }
                Tree::Node {
                    left,
                    value: v,
                    right: Box::new(new_right),
                }
            } else {
                Tree::Node { left, value: v, right }
            }
        }
    }
}
// </vc-code>

fn main() {}

}
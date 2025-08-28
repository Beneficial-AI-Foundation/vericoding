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
pub open spec fn contains_value(tree: Tree, val: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => false,
        Tree::Node { left, value, right } => {
            value == val || contains_value(*left, val) || contains_value(*right, val)
        }
    }
}

proof fn lemma_insert_preserves_min(tree: Tree, value: int, min_val: int)
    requires
        binary_search_tree(tree),
        min_value(tree, min_val),
        min_val < value,
    ensures
        min_value(insert_recursion(tree, value), min_val),
    decreases tree
{
    match tree {
        Tree::Empty => {}
        Tree::Node { left, right, value: node_val } => {
            if value < node_val {
                lemma_insert_preserves_min(*left, value, min_val);
            } else if value > node_val {
                lemma_insert_preserves_min(*right, value, min_val);
            }
        }
    }
}

proof fn lemma_insert_preserves_max(tree: Tree, value: int, max_val: int)
    requires
        binary_search_tree(tree),
        max_value(tree, max_val),
        max_val > value,
    ensures
        max_value(insert_recursion(tree, value), max_val),
    decreases tree
{
    match tree {
        Tree::Empty => {}
        Tree::Node { left, right, value: node_val } => {
            if value < node_val {
                lemma_insert_preserves_max(*left, value, max_val);
            } else if value > node_val {
                lemma_insert_preserves_max(*right, value, max_val);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn insert_recursion(tree: Tree, value: int) -> (res: Tree)
    requires binary_search_tree(tree),
    decreases tree,
    ensures res != Tree::Empty ==> binary_search_tree(res),
    ensures forall|x: int| min_value(tree, x) && x < value ==> min_value(res, x),
    ensures forall|x: int| max_value(tree, x) && x > value ==> max_value(res, x),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn insert_recursion(tree: Tree, value: int) -> (res: Tree)
    requires binary_search_tree(tree)
    decreases tree
    ensures res != Tree::Empty ==> binary_search_tree(res)
    ensures forall|x: int| min_value(tree, x) && x < value ==> min_value(res, x)
    ensures forall|x: int| max_value(tree, x) && x > value ==> max_value(res, x)
{
    match tree {
        Tree::Empty => {
            Tree::Node {
                left: Box::new(Tree::Empty),
                value: value,
                right: Box::new(Tree::Empty),
            }
        }
        Tree::Node { left, value: node_val, right } => {
            if value < node_val {
                let new_left = insert_recursion(*left, value);
                Tree::Node {
                    left: Box::new(new_left),
                    value: node_val,
                    right: right,
                }
            } else if value > node_val {
                let new_right = insert_recursion(*right, value);
                Tree::Node {
                    left: left,
                    value: node_val,
                    right: Box::new(new_right),
                }
            } else {
                tree
            }
        }
    }
}
// </vc-code>

fn main() {}

}
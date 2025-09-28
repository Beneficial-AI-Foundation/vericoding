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
impl Tree {
    pub open spec fn contains_value(&self, val: int) -> bool
        decreases self
    {
        match self {
            Tree::Empty => false,
            Tree::Node { left, value, right } => {
                *value == val || left.contains_value(val) || right.contains_value(val)
            }
        }
    }

    pub open spec fn make_node(left: Tree, value: int, right: Tree) -> Tree {
        Tree::Node {
            left: Box::new(left),
            value,
            right: Box::new(right),
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
        },
        Tree::Node { left, value: current_value, right } => {
            if value < current_value {
                let new_left = insert_recursion(*left, value);
                Proof {
                    assert(binary_search_tree(new_left));
                    assert(max_value(*left, current_value));
                    assert(current_value > value);
                    assert(max_value(new_left, current_value));
                    assert(min_value(*right, current_value));
                }
                Tree::Node {
                    left: Box::new(new_left),
                    value: current_value,
                    right,
                }
            } else if value > current_value {
                let new_right = insert_recursion(*right, value);
                Proof {
                    assert(binary_search_tree(new_right));
                    assert(min_value(*right, current_value));
                    assert(current_value < value);
                    assert(min_value(new_right, current_value));
                    assert(max_value(*left, current_value));
                }
                Tree::Node {
                    left,
                    value: current_value,
                    right: Box::new(new_right),
                }
            } else {
                // Value already exists, return the same tree
                tree
            }
        }
    }
}
// </vc-code>

fn main() {}

}
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
proof fn lemma_node_bst(left: Tree, value: int, right: Tree)
    requires
        binary_search_tree(left),
        binary_search_tree(right),
        max_value(left, value),
        min_value(right, value),
    ensures
        binary_search_tree(Tree::Node { left: Box::new(left), value, right: Box::new(right) }),
{
    if left.is_Empty() {
        // Left subtree is empty, condition holds
    } else {
        let root_value = left.get_Node_value();
        assert(value > root_value); // From max_value(left, value)
    }
    if right.is_Empty() {
        // Right subtree is empty, condition holds
    } else {
        let root_value = right.get_Node_value();
        assert(value < root_value); // From min_value(right, value)
    }
    // All conditions for binary_search_tree are satisfied
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
        Tree::Node { left, value: current, right } => {
            if value < current {
                let new_left = insert_recursion(*left, value);
                assert(max_value(*left, current));
                assert(current > value);
                assert(max_value(new_left, current));
                let new_node = Tree::Node {
                    left: Box::new(new_left),
                    value: current,
                    right: right,
                };
                lemma_node_bst(new_left, current, *right);
                new_node
            } else if value > current {
                let new_right = insert_recursion(*right, value);
                assert(min_value(*right, current));
                assert(value > current);
                assert(min_value(new_right, current));
                let new_node = Tree::Node {
                    left: left,
                    value: current,
                    right: Box::new(new_right),
                };
                lemma_node_bst(*left, current, new_right);
                new_node
            } else {
                Tree::Node { left, value: current, right }
            }
        }
    }
}
// </vc-code>

fn main() {}

}
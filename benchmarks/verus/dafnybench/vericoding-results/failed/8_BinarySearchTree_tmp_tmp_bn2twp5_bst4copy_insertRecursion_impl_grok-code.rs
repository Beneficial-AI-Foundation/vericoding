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
#[verifier::proof]
pub fn lemma_insert_preserves_max_value(tree: Tree, value: int, v: int)
    requires value < v
    requires max_value(tree, v)
    ensures max_value(insert_recursion(tree, value), v)
    decreases tree
{
    match tree {
        Tree::Empty => {
            assert(max_value(Tree::Node { left: Box::new(Tree::Empty), value, right: Box::new(Tree::Empty) }, v) == (v > value && max_value(Tree::Empty, v) && max_value(Tree::Empty, v)));
        },
        Tree::Node { left: l, value: t_v, right: r } => {
            if value < t_v {
                lemma_insert_preserves_max_value(*l, value, v);
                assert(max_value(Tree::Node { left: Box::new(insert_recursion(*l, value)), value: t_v, right: Box::new(r) }, v) == (v > t_v && max_value(insert_recursion(*l, value), v) && max_value(*r, v)));
            } else if value > t_v {
                lemma_insert_preserves_max_value(*r, value, v);
                assert(max_value(Tree::Node { left: Box::new(l), value: t_v, right: Box::new(insert_recursion(*r, value)) }, v) == (v > t_v && max_value(*l, v) && max_value(insert_recursion(*r, value), v)));
            } else {
                // value == t_v, insert to right
                lemma_insert_preserves_max_value(*r, value, v);
                assert(max_value(Tree::Node { left: Box::new(l), value: t_v, right: Box::new(insert_recursion(*r, value)) }, v) == (v > t_v && max_value(*l, v) && max_value(insert_recursion(*r, value), v)));
            }
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
        Tree::Empty => Tree::Node { left: Box::new(Tree::Empty), value, right: Box::new(Tree::Empty) },
        Tree::Node { left, value: v_tree, right } => {
            if value < v_tree {
                Tree::Node { left: Box::new(insert_recursion(*left, value)), value: v_tree, right }
            } else {
                Tree::Node { left, value: v_tree, right: Box::new(insert_recursion(*right, value)) }
            }
        }
    }
}
// </vc-code>

fn main() {}

}
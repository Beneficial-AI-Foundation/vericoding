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
proof fn lemma_insert_preserves_bst(tree: Tree, value: int, left: Box<Tree>, node_value: int, right: Box<Tree>)
    requires 
        binary_search_tree(tree),
        tree == (Tree::Node { left: left, value: node_value, right: right }),
        value < node_value,
        binary_search_tree(insert_recursion(*left, value))
    ensures binary_search_tree(Tree::Node { left: Box::new(insert_recursion(*left, value)), value: node_value, right: right })
{
}

proof fn lemma_insert_preserves_bst_right(tree: Tree, value: int, left: Box<Tree>, node_value: int, right: Box<Tree>)
    requires 
        binary_search_tree(tree),
        tree == (Tree::Node { left: left, value: node_value, right: right }),
        value > node_value,
        binary_search_tree(insert_recursion(*right, value))
    ensures binary_search_tree(Tree::Node { left: left, value: node_value, right: Box::new(insert_recursion(*right, value)) })
{
}

proof fn lemma_min_value_preserved(tree: Tree, value: int, x: int)
    requires binary_search_tree(tree), min_value(tree, x), x < value
    ensures min_value(insert_recursion(tree, value), x)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                lemma_min_value_preserved(*left, value, x);
            } else if value > node_value {
                lemma_min_value_preserved(*right, value, x);
            }
        }
    }
}

proof fn lemma_max_value_preserved(tree: Tree, value: int, x: int)
    requires binary_search_tree(tree), max_value(tree, x), x > value
    ensures max_value(insert_recursion(tree, value), x)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                lemma_max_value_preserved(*left, value, x);
            } else if value > node_value {
                lemma_max_value_preserved(*right, value, x);
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
{
    match tree {
        Tree::Empty => Tree::Node { left: Box::new(Tree::Empty), value: value, right: Box::new(Tree::Empty) },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                let new_left = insert_recursion(*left, value);
                proof {
                    lemma_insert_preserves_bst(tree, value, left, node_value, right);
                }
                Tree::Node { left: Box::new(new_left), value: node_value, right: right }
            } else if value > node_value {
                let new_right = insert_recursion(*right, value);
                proof {
                    lemma_insert_preserves_bst_right(tree, value, left, node_value, right);
                }
                Tree::Node { left: left, value: node_value, right: Box::new(new_right) }
            } else {
                tree
            }
        }
    }
}
// </vc-code>

fn main() {}

}
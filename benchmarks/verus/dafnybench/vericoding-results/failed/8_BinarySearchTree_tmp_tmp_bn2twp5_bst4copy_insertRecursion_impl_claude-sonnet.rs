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
proof fn lemma_min_value_preserved(tree: Tree, x: int, value: int)
    requires min_value(tree, x) && x < value,
    ensures min_value(tree, value) ==> min_value(tree, x),
    decreases tree,
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: v, right } => {
            lemma_min_value_preserved(*left, x, value);
            lemma_min_value_preserved(*right, x, value);
        }
    }
}

proof fn lemma_max_value_preserved(tree: Tree, x: int, value: int)
    requires max_value(tree, x) && x > value,
    ensures max_value(tree, value) ==> max_value(tree, x),
    decreases tree,
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: v, right } => {
            lemma_max_value_preserved(*left, x, value);
            lemma_max_value_preserved(*right, x, value);
        }
    }
}

proof fn lemma_bst_min_max(tree: Tree, value: int)
    requires binary_search_tree(tree),
    decreases tree,
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: v, right } => {
            lemma_bst_min_max(*left, value);
            lemma_bst_min_max(*right, value);
        }
    }
}

pub open spec fn tree_contains_value(tree: Tree, value: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => false,
        Tree::Node { left, value: v, right } => {
            v == value || tree_contains_value(*left, value) || tree_contains_value(*right, value)
        }
    }
}

proof fn lemma_insert_preserves_bst(tree: Tree, value: int, result: Tree)
    requires binary_search_tree(tree),
    requires result == insert_recursion_spec(tree, value),
    ensures binary_search_tree(result),
    decreases tree,
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: v, right } => {
            if value < v {
                lemma_insert_preserves_bst(*left, value, insert_recursion_spec(*left, value));
            } else if value > v {
                lemma_insert_preserves_bst(*right, value, insert_recursion_spec(*right, value));
            }
        }
    }
}

pub open spec fn insert_recursion_spec(tree: Tree, value: int) -> Tree
    decreases tree
{
    match tree {
        Tree::Empty => Tree::Node {
            left: Box::new(Tree::Empty),
            value: value,
            right: Box::new(Tree::Empty),
        },
        Tree::Node { left, value: v, right } => {
            if value < v {
                Tree::Node {
                    left: Box::new(insert_recursion_spec(*left, value)),
                    value: v,
                    right: right,
                }
            } else if value > v {
                Tree::Node {
                    left: left,
                    value: v,
                    right: Box::new(insert_recursion_spec(*right, value)),
                }
            } else {
                tree
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
        Tree::Empty => {
            let result = Tree::Node {
                left: Box::new(Tree::Empty),
                value: value,
                right: Box::new(Tree::Empty),
            };
            proof {
                assert(binary_search_tree(result));
            }
            result
        },
        Tree::Node { left, value: v, right } => {
            if value < v {
                let new_left = insert_recursion(*left, value);
                proof {
                    assert(binary_search_tree(*left));
                    assert(binary_search_tree(new_left));
                    assert(max_value(*left, v));
                    assert(max_value(new_left, v));
                    assert(min_value(*right, v));
                }
                Tree::Node {
                    left: Box::new(new_left),
                    value: v,
                    right: right,
                }
            } else if value > v {
                let new_right = insert_recursion(*right, value);
                proof {
                    assert(binary_search_tree(*right));
                    assert(binary_search_tree(new_right));
                    assert(min_value(*right, v));
                    assert(min_value(new_right, v));
                    assert(max_value(*left, v));
                }
                Tree::Node {
                    left: left,
                    value: v,
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
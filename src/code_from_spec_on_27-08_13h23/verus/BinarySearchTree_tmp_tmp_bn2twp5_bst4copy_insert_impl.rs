use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub enum Tree {
    Empty,
    Node(Box<Tree>, int, Box<Tree>),
}

pub open spec fn binary_search_tree(tree: Tree) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, value, right) => {
            (matches!(*left, Tree::Empty) || (*left).get_node_value() < value)
            && (matches!(*right, Tree::Empty) || (*right).get_node_value() > value)
            && binary_search_tree(*left)
            && binary_search_tree(*right)
            && min_value(*right, value)
            && max_value(*left, value)
        }
    }
}

pub open spec fn max_value(tree: Tree, max: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, value, right) => {
            max > value && max_value(*left, max) && max_value(*right, max)
        }
    }
}

pub open spec fn min_value(tree: Tree, min: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => true,
        Tree::Node(left, value, right) => {
            min < value && min_value(*left, min) && min_value(*right, min)
        }
    }
}

impl Tree {
    pub open spec fn get_node_value(self) -> int
        recommends !matches!(self, Tree::Empty)
    {
        match self {
            Tree::Node(_, value, _) => value,
            _ => arbitrary()
        }
    }
}

fn insert_recursion(tree: Tree, value: int) -> (res: Tree)
    requires binary_search_tree(tree),
    ensures 
        res != Tree::Empty ==> binary_search_tree(res),
        forall|x: int| min_value(tree, x) && x < value ==> min_value(res, x),
        forall|x: int| max_value(tree, x) && x > value ==> max_value(res, x),
    decreases tree,
{
    assume(false);
    Tree::Empty
}

// <vc-helpers>
pub open spec fn contains_value(tree: Tree, value: int) -> bool
    decreases tree
{
    match tree {
        Tree::Empty => false,
        Tree::Node(left, node_value, right) => {
            node_value == value || contains_value(*left, value) || contains_value(*right, value)
        }
    }
}

pub proof fn lemma_insert_preserves_min_max(tree: Tree, value: int, min: int, max: int)
    requires 
        binary_search_tree(tree),
        min_value(tree, min),
        max_value(tree, max),
        min < value,
        max > value,
    ensures
        min_value(insert_recursion(tree, value), min),
        max_value(insert_recursion(tree, value), max),
    decreases tree
{
    match tree {
        Tree::Empty => {}
        Tree::Node(left, node_value, right) => {
            if value < node_value {
                lemma_insert_preserves_min_max(*left, value, min, node_value);
            } else if value > node_value {
                lemma_insert_preserves_min_max(*right, value, node_value, max);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn insert(tree: Tree, value: int) -> (res: Tree)
    requires binary_search_tree(tree),
    ensures binary_search_tree(res),
    decreases tree,
// </vc-spec>
// </vc-spec>

// <vc-code>
pub fn insert(tree: Tree, value: int) -> (res: Tree)
    requires binary_search_tree(tree),
    ensures binary_search_tree(res),
    decreases tree
{
    insert_recursion(tree, value)
}

fn insert_recursion(tree: Tree, value: int) -> (res: Tree)
    requires binary_search_tree(tree),
    ensures 
        res != Tree::Empty ==> binary_search_tree(res),
        forall|x: int| min_value(tree, x) && x < value ==> min_value(res, x),
        forall|x: int| max_value(tree, x) && x > value ==> max_value(res, x),
    decreases tree
{
    match tree {
        Tree::Empty => {
            Tree::Node(Box::new(Tree::Empty), value, Box::new(Tree::Empty))
        }
        Tree::Node(left, node_value, right) => {
            if value < node_value {
                let new_left = insert_recursion(*left, value);
                Tree::Node(Box::new(new_left), node_value, right)
            } else if value > node_value {
                let new_right = insert_recursion(*right, value);
                Tree::Node(left, node_value, Box::new(new_right))
            } else {
                tree
            }
        }
    }
}
// </vc-code>

fn main() {}

}
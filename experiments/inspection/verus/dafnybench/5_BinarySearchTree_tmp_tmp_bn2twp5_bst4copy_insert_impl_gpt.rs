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

// </vc-helpers>

// <vc-spec>
fn insert(tree: Tree, value: int) -> (res: Tree)
    requires binary_search_tree(tree),
    ensures binary_search_tree(res),
    decreases tree,
// </vc-spec>
// <vc-code>
{
    let res = insert_recursion(tree, value);
    match res {
        Tree::Empty => {
            proof {
                assert(binary_search_tree(Tree::Empty));
            }
            Tree::Empty
        }
        res2 @ Tree::Node(_, _, _) => {
            proof {
                assert(binary_search_tree(res2));
            }
            res2
        }
    }
}
// </vc-code>

fn main() {}

}
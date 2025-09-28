// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added property and monotonicity lemmas for spec functions */
proof fn max_value_implies_less(tree: Tree, m: int)
    requires
        !tree.is_Empty(),
        max_value(tree, m),
    ensures
        tree.get_Node_value() < m,
    decreases tree
{
}

proof fn min_value_implies_greater(tree: Tree, m: int)
    requires
        !tree.is_Empty(),
        min_value(tree, m),
    ensures
        m < tree.get_Node_value(),
    decreases tree
{
}

proof fn max_value_mono(tree: Tree, m1: int, m2: int)
    requires
        max_value(tree, m1),
        m1 <= m2,
    ensures
        max_value(tree, m2),
    decreases tree
{
    match tree {
        Tree::Empty => {}
        Tree::Node { left, value, right } => {
            assert(m2 >= m1);
            assert(m1 > value);
            assert(m2 > value);
            max_value_mono(*left, m1, m2);
            max_value_mono(*right, m1, m2);
        }
    }
}

proof fn min_value_mono(tree: Tree, m1: int, m2: int)
    requires
        min_value(tree, m1),
        m1 >= m2,
    ensures
        min_value(tree, m2),
    decreases tree
{
    match tree {
        Tree::Empty => {}
        Tree::Node { left, value, right } => {
            assert(m2 <= m1);
            assert(m1 < value);
            assert(m2 < value);
            min_value_mono(*left, m1, m2);
            min_value_mono(*right, m1, m2);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn insert_recursion(tree: Tree, value: int) -> (res: Tree)
    requires binary_search_tree(tree)
    ensures 
        res != Tree::Empty ==> binary_search_tree(res),
        forall|x: int| min_value(tree, x) && x < value ==> min_value(res, x),
        forall|x: int| max_value(tree, x) && x > value ==> max_value(res, x)
    decreases tree
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error in the Empty case by removing the invalid proof block */
{
    match tree {
        Tree::Empty => {
            let res = Tree::Node {
                left: Box::new(Tree::Empty),
                value: value,
                right: Box::new(Tree::Empty),
            };
            res
        }
        Tree::Node { left, value: v, right } => {
            if value < v {
                let new_left = insert_recursion(*left, value);
                let res = Tree::Node {
                    left: Box::new(new_left),
                    value: v,
                    right: right,
                };
                proof {
                    assert(max_value(new_left, v));
                    if !new_left.is_Empty() {
                        max_value_implies_less(new_left, v);
                    }
                    assert(binary_search_tree(res));

                    assert forall|x: int| min_value(tree, x) && x < value implies min_value(res, x) by {
                        assert(min_value(new_left, x));
                        assert(min_value(res, x));
                    }
                    assert forall|x: int| max_value(tree, x) && x > value implies max_value(res, x) by {
                        assert(max_value(new_left, x));
                        assert(max_value(res, x));
                    }
                }
                res
            } else if value > v {
                let new_right = insert_recursion(*right, value);
                let res = Tree::Node {
                    left: left,
                    value: v,
                    right: Box::new(new_right),
                };
                proof {
                    assert(min_value(new_right, v));
                    if !new_right.is_Empty() {
                        min_value_implies_greater(new_right, v);
                    }
                    assert(binary_search_tree(res));
                    assert forall|x: int| min_value(tree, x) && x < value implies min_value(res, x) by {
                        assert(min_value(new_right, x));
                        assert(min_value(res, x));
                    }
                    assert forall|x: int| max_value(tree, x) && x > value implies max_value(res, x) by {
                        assert(max_value(new_right, x));
                        assert(max_value(res, x));
                    }
                }
                res
            } else {
                Tree::Node { left: left, value: v, right: right }
            }
        }
    }
}
// </vc-code>

}
fn main() {}
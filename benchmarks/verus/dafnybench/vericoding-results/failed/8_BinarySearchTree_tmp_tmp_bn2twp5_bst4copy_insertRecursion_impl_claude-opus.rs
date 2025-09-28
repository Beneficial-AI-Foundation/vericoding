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
// Helper lemmas for proving BST properties after insertion

proof fn lemma_min_value_preserved(tree: Tree, min: int, value: int)
    requires
        min < value,
        min_value(tree, min),
    ensures
        min_value(tree, min),
    decreases tree,
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: v, right } => {
            lemma_min_value_preserved(*left, min, value);
            lemma_min_value_preserved(*right, min, value);
        }
    }
}

proof fn lemma_max_value_preserved(tree: Tree, max: int, value: int)
    requires
        max > value,
        max_value(tree, max),
    ensures
        max_value(tree, max),
    decreases tree,
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: v, right } => {
            lemma_max_value_preserved(*left, max, value);
            lemma_max_value_preserved(*right, max, value);
        }
    }
}

proof fn lemma_insert_maintains_min(tree: Tree, value: int, res: Tree, min: int)
    requires
        binary_search_tree(tree),
        min < value,
        min_value(tree, min),
        res == insert_recursion_spec(tree, value),
    ensures
        min_value(res, min),
    decreases tree,
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                lemma_insert_maintains_min(*left, value, insert_recursion_spec(*left, value), min);
            } else if value > node_value {
                lemma_insert_maintains_min(*right, value, insert_recursion_spec(*right, value), min);
            }
        }
    }
}

proof fn lemma_insert_maintains_max(tree: Tree, value: int, res: Tree, max: int)
    requires
        binary_search_tree(tree),
        max > value,
        max_value(tree, max),
        res == insert_recursion_spec(tree, value),
    ensures
        max_value(res, max),
    decreases tree,
{
    match tree {
        Tree::Empty => {},
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                lemma_insert_maintains_max(*left, value, insert_recursion_spec(*left, value), max);
            } else if value > node_value {
                lemma_insert_maintains_max(*right, value, insert_recursion_spec(*right, value), max);
            }
        }
    }
}

spec fn insert_recursion_spec(tree: Tree, value: int) -> Tree
    decreases tree,
{
    match tree {
        Tree::Empty => Tree::Node {
            left: Box::new(Tree::Empty),
            value: value,
            right: Box::new(Tree::Empty),
        },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                Tree::Node {
                    left: Box::new(insert_recursion_spec(*left, value)),
                    value: node_value,
                    right: right,
                }
            } else if value > node_value {
                Tree::Node {
                    left: left,
                    value: node_value,
                    right: Box::new(insert_recursion_spec(*right, value)),
                }
            } else {
                Tree::Node {
                    left: left,
                    value: node_value,
                    right: right,
                }
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
            Tree::Node {
                left: Box::new(Tree::Empty),
                value: value,
                right: Box::new(Tree::Empty),
            }
        },
        Tree::Node { left, value: node_value, right } => {
            if value < node_value {
                let new_left = insert_recursion(*left, value);
                
                proof {
                    assert(new_left != Tree::Empty);
                    assert(binary_search_tree(new_left));
                    
                    assert forall|x: int| max_value(*left, x) && x > value implies max_value(new_left, x) by {
                        lemma_insert_maintains_max(*left, value, new_left, x);
                    }
                    
                    assert(max_value(*left, node_value));
                    assert(max_value(new_left, node_value));
                    assert(new_left.is_Empty() || new_left.get_Node_value() < node_value);
                    
                    assert forall|x: int| min_value(tree, x) && x < value implies min_value(
                        Tree::Node { left: Box::new(new_left), value: node_value, right: right.clone() }, x
                    ) by {
                        if x < node_value {
                            lemma_insert_maintains_min(*left, value, new_left, x);
                        }
                    }
                }
                
                Tree::Node {
                    left: Box::new(new_left),
                    value: node_value,
                    right: right,
                }
            } else if value > node_value {
                let new_right = insert_recursion(*right, value);
                
                proof {
                    assert(new_right != Tree::Empty);
                    assert(binary_search_tree(new_right));
                    
                    assert forall|x: int| min_value(*right, x) && x < value implies min_value(new_right, x) by {
                        lemma_insert_maintains_min(*right, value, new_right, x);
                    }
                    
                    assert(min_value(*right, node_value));
                    assert(min_value(new_right, node_value));
                    assert(new_right.is_Empty() || new_right.get_Node_value() > node_value);
                    
                    assert forall|x: int| max_value(tree, x) && x > value implies max_value(
                        Tree::Node { left: left.clone(), value: node_value, right: Box::new(new_right) }, x
                    ) by {
                        if x > node_value {
                            lemma_insert_maintains_max(*right, value, new_right, x);
                        }
                    }
                }
                
                Tree::Node {
                    left: left,
                    value: node_value,
                    right: Box::new(new_right),
                }
            } else {
                Tree::Node {
                    left: left,
                    value: node_value,
                    right: right,
                }
            }
        }
    }
}
// </vc-code>

fn main() {}

}
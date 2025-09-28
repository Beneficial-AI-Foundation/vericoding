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
pub proof fn instantiate_max_from_forall(old: Tree, value: int, new: Tree, x: int)
    requires forall|y: int| #[trigger] max_value(old, y) && y > value ==> max_value(new, y),
    requires max_value(old, x) && x > value,
    ensures max_value(new, x)
{
    // Instantiate the universal implication with x
    assert(max_value(new, x));
}

pub proof fn instantiate_min_from_forall(old: Tree, value: int, new: Tree, x: int)
    requires forall|y: int| #[trigger] min_value(old, y) && y < value ==> min_value(new, y),
    requires min_value(old, x) && x < value,
    ensures min_value(new, x)
{
    // Instantiate the universal implication with x
    assert(min_value(new, x));
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
            let res = Tree::Node { left: Box::new(Tree::Empty), value: value, right: Box::new(Tree::Empty) };
            proof {
                // Show the single-node tree is a BST
                assert(res.is_Empty() == false);
                assert(binary_search_tree(res));
                // The other ensures about min/max follow trivially for an inserted singleton.
            }
            res
        }
        Tree::Node { left, value: v, right } => {
            if value < v {
                let new_left = insert_recursion(*left, value);
                let res = Tree::Node { left: Box::new(new_left), value: v, right };
                proof {
                    // From the precondition binary_search_tree(Tree::Node { left, v, right })
                    assert(max_value(*left, v));
                    assert(min_value(*right, v));
                    assert(binary_search_tree(*left));
                    assert(binary_search_tree(*right));

                    // From the recursive postconditions on new_left we have:
                    // 1) new_left != Empty ==> binary_search_tree(new_left)
                    // 2) forall x. max_value(*left, x) && x > value ==> max_value(new_left, x)
                    assert(new_left.is_Empty() || binary_search_tree(new_left));

                    // Instantiate the recursive universal postcondition to get max_value(new_left, v):
                    instantiate_max_from_forall(*left, value, new_left, v);

                    // Root constraint for res: new_left root < v (if non-empty)
                    assert(new_left.is_Empty() || new_left.get_Node_value() < v);
                    // Right root constraint from original tree
                    assert(right.is_Empty() || right.get_Node_value() > v);
                    // Subtrees are BSTs
                    assert(new_left.is_Empty() || binary_search_tree(new_left));
                    assert(binary_search_tree(*right));
                    // Hence res is a BST
                    assert(binary_search_tree(res));
                }
                res
            } else if value > v {
                let new_right = insert_recursion(*right, value);
                let res = Tree::Node { left, value: v, right: Box::new(new_right) };
                proof {
                    // From the precondition binary_search_tree(Tree::Node { left, v, right })
                    assert(max_value(*left, v));
                    assert(min_value(*right, v));
                    assert(binary_search_tree(*left));
                    assert(binary_search_tree(*right));

                    assert(new_right.is_Empty() || binary_search_tree(new_right));

                    // Instantiate the recursive universal postcondition for the right subtree:
                    instantiate_min_from_forall(*right, value, new_right, v);

                    // Root constraints for res
                    assert(left.is_Empty() || left.get_Node_value() < v);
                    assert(new_right.is_Empty() || new_right.get_Node_value() > v);
                    assert(binary_search_tree(*left));
                    assert(new_right.is_Empty() || binary_search_tree(new_right));
                    assert(binary_search_tree(res));
                }
                res
            } else {
                // value == v: no insertion, return original node
                let res = Tree::Node { left, value: v, right };
                proof {
                    // Original tree is already a BST; returning it preserves all properties.
                    assert(binary_search_tree(res));
                }
                res
            }
        }
    }
}
// </vc-code>

fn main() {}

}
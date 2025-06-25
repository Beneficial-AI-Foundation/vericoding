pub enum Tree {
    Empty,
    Node { left: Box<Tree>, value: i32, right: Box<Tree> }
}

pub open spec fn binary_search_tree(tree: Tree) -> bool {
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

pub open spec fn max_value(tree: Tree, max: i32) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => {
            (max > v) && max_value(*left, max) && max_value(*right, max)
        }
    }
}

pub open spec fn min_value(tree: Tree, min: i32) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => {
            (min < v) && min_value(*left, min) && min_value(*right, min)
        }
    }
}

pub fn insert(tree: Tree, value: i32) -> (res: Tree)
    requires(binary_search_tree(tree))
    ensures(binary_search_tree(res))
{
}

pub fn insert_recursion(tree: Tree, value: i32) -> (res: Tree)
    requires(binary_search_tree(tree))
    ensures(res != Tree::Empty ==> binary_search_tree(res))
    ensures(forall|x: i32| min_value(tree, x) && x < value ==> min_value(res, x))
    ensures(forall|x: i32| max_value(tree, x) && x > value ==> max_value(res, x))
{
}
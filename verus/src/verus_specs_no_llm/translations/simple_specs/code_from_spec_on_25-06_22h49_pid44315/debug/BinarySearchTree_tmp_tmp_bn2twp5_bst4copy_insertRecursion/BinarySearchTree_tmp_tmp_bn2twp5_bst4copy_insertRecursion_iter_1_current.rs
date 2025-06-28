use builtin::*;
use builtin_macros::*;

verus! {

// Define the Tree enum
enum Tree {
    Empty,
    Node(Box<Tree>, int, Box<Tree>),
}

fn main() {
}

spec fn BinarySearchTree(tree: Tree) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, value, right) => {
            (left.is_Empty() || left.get_value() < value)
            && (right.is_Empty() || right.get_value() > value)
            && BinarySearchTree(*left) && BinarySearchTree(*right)
            && minValue(*right, value) && maxValue(*left, value)
        }
    }
}

spec fn minValue(tree: Tree, min: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => (min < v) && minValue(*left, min) && minValue(*right, min)
    }
}

spec fn maxValue(tree: Tree, max: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => (max > v) && maxValue(*left, max) && maxValue(*right, max)
    }
}

// Helper functions for cleaner code
spec fn Tree::is_Empty(self) -> bool {
    matches!(self, Tree::Empty)
}

spec fn Tree::get_value(self) -> int 
    requires !self.is_Empty()
{
    match self {
        Tree::Node(_, v, _) => v,
        Tree::Empty => arbitrary(), // unreachable due to precondition
    }
}

fn insertRecursion(tree: Tree, value: int) -> (res: Tree)
    requires
        BinarySearchTree(tree)
    ensures
        res != Tree::Empty ==> BinarySearchTree(res),
        forall|x: int| minValue(tree, x) && x < value ==> minValue(res, x),
        forall|x: int| maxValue(tree, x) && x > value ==> maxValue(res, x)
{
    match tree {
        Tree::Empty => {
            Tree::Node(Box::new(Tree::Empty), value, Box::new(Tree::Empty))
        },
        Tree::Node(left, v, right) => {
            if value < v {
                let new_left = insertRecursion(*left, value);
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
                let new_right = insertRecursion(*right, value);
                Tree::Node(left, v, Box::new(new_right))
            } else {
                // value == v, don't insert duplicates
                tree
            }
        }
    }
}

}
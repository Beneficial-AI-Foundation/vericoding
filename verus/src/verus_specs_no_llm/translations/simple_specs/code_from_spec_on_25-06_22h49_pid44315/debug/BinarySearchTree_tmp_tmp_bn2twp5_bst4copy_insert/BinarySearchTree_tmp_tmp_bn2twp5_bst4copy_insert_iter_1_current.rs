use builtin::*;
use builtin_macros::*;

verus! {

// Define the Tree enum
enum Tree {
    Empty,
    Node(Box<Tree>, int, Box<Tree>),
}

impl Tree {
    spec fn value(self) -> int 
        recommends matches!(self, Tree::Node(_, _, _))
    {
        match self {
            Tree::Node(_, v, _) => v,
            Tree::Empty => 0, // dummy value, should not be called
        }
    }
    
    spec fn left(self) -> Tree
        recommends matches!(self, Tree::Node(_, _, _))
    {
        match self {
            Tree::Node(left, _, _) => *left,
            Tree::Empty => Tree::Empty, // dummy value
        }
    }
    
    spec fn right(self) -> Tree
        recommends matches!(self, Tree::Node(_, _, _))
    {
        match self {
            Tree::Node(_, _, right) => *right,
            Tree::Empty => Tree::Empty, // dummy value
        }
    }
}

spec fn BinarySearchTree(tree: Tree) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            let left_tree = *left;
            let right_tree = *right;
            (left_tree == Tree::Empty || left_tree.value() < v)
            && (right_tree == Tree::Empty || right_tree.value() > v)
            && BinarySearchTree(left_tree) && BinarySearchTree(right_tree)
            && minValue(right_tree, v) && maxValue(left_tree, v)
        }
    }
}

spec fn maxValue(tree: Tree, max: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            (max > v) && maxValue(*left, max) && maxValue(*right, max)
        }
    }
}

spec fn minValue(tree: Tree, min: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            (min < v) && minValue(*left, min) && minValue(*right, min)
        }
    }
}

fn insertRecursion(tree: Tree, value: int) -> (res: Tree)
    requires BinarySearchTree(tree)
    ensures res != Tree::Empty ==> BinarySearchTree(res)
    ensures forall|x: int| minValue(tree, x) && x < value ==> minValue(res, x)
    ensures forall|x: int| maxValue(tree, x) && x > value ==> maxValue(res, x)
{
    match tree {
        Tree::Empty => Tree::Node(Box::new(Tree::Empty), value, Box::new(Tree::Empty)),
        Tree::Node(left, v, right) => {
            if value < v {
                let new_left = insertRecursion(*left, value);
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
                let new_right = insertRecursion(*right, value);
                Tree::Node(left, v, Box::new(new_right))
            } else {
                // Value already exists, return original tree
                tree
            }
        }
    }
}

fn insert(tree: Tree, value: int) -> (res: Tree)
    requires BinarySearchTree(tree)
    ensures res != Tree::Empty ==> BinarySearchTree(res)
    ensures forall|x: int| minValue(tree, x) && x < value ==> minValue(res, x)
    ensures forall|x: int| maxValue(tree, x) && x > value ==> maxValue(res, x)
    ensures BinarySearchTree(res)
{
    insertRecursion(tree, value)
}

fn main() {
    let empty_tree = Tree::Empty;
    let tree_with_5 = insert(empty_tree, 5);
    let tree_with_3_and_5 = insert(tree_with_5, 3);
    let final_tree = insert(tree_with_3_and_5, 7);
}

}
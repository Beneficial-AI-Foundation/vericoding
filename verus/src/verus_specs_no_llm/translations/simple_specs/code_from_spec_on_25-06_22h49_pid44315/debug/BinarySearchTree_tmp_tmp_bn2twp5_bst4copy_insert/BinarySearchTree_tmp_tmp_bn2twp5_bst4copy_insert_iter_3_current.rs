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
            BinarySearchTree(left_tree) && BinarySearchTree(right_tree)
            && maxValue(left_tree, v) && minValue(right_tree, v)
        }
    }
}

spec fn maxValue(tree: Tree, max: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            v < max && maxValue(*left, max) && maxValue(*right, max)
        }
    }
}

spec fn minValue(tree: Tree, min: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node(left, v, right) => {
            v > min && minValue(*left, min) && minValue(*right, min)
        }
    }
}

proof fn lemma_insert_preserves_max(tree: Tree, value: int, max: int)
    requires BinarySearchTree(tree) && maxValue(tree, max) && value < max
    ensures maxValue(insertRecursion(tree, value), max)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_insert_preserves_max(*left, value, max);
            } else if value > v {
                lemma_insert_preserves_max(*right, value, max);
            }
        }
    }
}

proof fn lemma_insert_preserves_min(tree: Tree, value: int, min: int)
    requires BinarySearchTree(tree) && minValue(tree, min) && value > min
    ensures minValue(insertRecursion(tree, value), min)
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_insert_preserves_min(*left, value, min);
            } else if value > v {
                lemma_insert_preserves_min(*right, value, min);
            }
        }
    }
}

proof fn lemma_insert_preserves_bst(tree: Tree, value: int)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(insertRecursion(tree, value))
    decreases tree
{
    match tree {
        Tree::Empty => {},
        Tree::Node(left, v, right) => {
            if value < v {
                lemma_insert_preserves_bst(*left, value);
                lemma_insert_preserves_max(*left, value, v);
            } else if value > v {
                lemma_insert_preserves_bst(*right, value);
                lemma_insert_preserves_min(*right, value, v);
            }
        }
    }
}

fn insertRecursion(tree: Tree, value: int) -> (res: Tree)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(res)
    ensures forall|x: int| minValue(tree, x) && x < value ==> minValue(res, x)
    ensures forall|x: int| maxValue(tree, x) && x > value ==> maxValue(res, x)
    decreases tree
{
    match tree {
        Tree::Empty => Tree::Node(Box::new(Tree::Empty), value, Box::new(Tree::Empty)),
        Tree::Node(left, v, right) => {
            if value < v {
                let new_left = insertRecursion(*left, value);
                proof {
                    lemma_insert_preserves_bst(*left, value);
                    lemma_insert_preserves_max(*left, value, v);
                    assert(BinarySearchTree(new_left));
                    assert(maxValue(new_left, v));
                    assert(forall|x: int| minValue(tree, x) && x < value ==> minValue(new_left, x)) by {
                        assert forall|x: int| minValue(tree, x) && x < value implies minValue(new_left, x) by {
                            lemma_insert_preserves_min(*left, value, x);
                        }
                    };
                    assert(forall|x: int| maxValue(tree, x) && x > value ==> maxValue(new_left, x)) by {
                        assert forall|x: int| maxValue(tree, x) && x > value implies maxValue(new_left, x) by {
                            lemma_insert_preserves_max(*left, value, x);
                        }
                    };
                }
                Tree::Node(Box::new(new_left), v, right)
            } else if value > v {
                let new_right = insertRecursion(*right, value);
                proof {
                    lemma_insert_preserves_bst(*right, value);
                    lemma_insert_preserves_min(*right, value, v);
                    assert(BinarySearchTree(new_right));
                    assert(minValue(new_right, v));
                    assert(forall|x: int| minValue(tree, x) && x < value ==> minValue(new_right, x)) by {
                        assert forall|x: int| minValue(tree, x) && x < value implies minValue(new_right, x) by {
                            lemma_insert_preserves_min(*right, value, x);
                        }
                    };
                    assert(forall|x: int| maxValue(tree, x) && x > value ==> maxValue(new_right, x)) by {
                        assert forall|x: int| maxValue(tree, x) && x > value implies maxValue(new_right, x) by {
                            lemma_insert_preserves_max(*right, value, x);
                        }
                    };
                }
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
    ensures BinarySearchTree(res)
    ensures forall|x: int| minValue(tree, x) && x < value ==> minValue(res, x)
    ensures forall|x: int| maxValue(tree, x) && x > value ==> maxValue(res, x)
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
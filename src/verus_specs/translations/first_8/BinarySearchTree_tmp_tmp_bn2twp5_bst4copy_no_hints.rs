//ATOM
pub enum Tree {
    Empty,
    Node { left: Box<Tree>, value: int, right: Box<Tree> }
}

//ATOM
pub spec fn BinarySearchTree(tree: Tree) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value, right } => {
            ((*left == Tree::Empty) || (left.get_Node_value() < value))
            && ((*right == Tree::Empty) || (right.get_Node_value() > value))
            && BinarySearchTree(*left) && BinarySearchTree(*right)
            && minValue(*right, value) && maxValue(*left, value)
        }
    }
}

//ATOM
pub spec fn maxValue(tree: Tree, max: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => (max > v) && maxValue(*left, max) && maxValue(*right, max)
    }
}

//ATOM
pub spec fn minValue(tree: Tree, min: int) -> bool {
    match tree {
        Tree::Empty => true,
        Tree::Node { left, value: v, right } => (min < v) && minValue(*left, min) && minValue(*right, min)
    }
}

//SPEC
pub fn GetMin(tree: Tree) -> (res: int)
    requires(BinarySearchTree(tree))
    ensures(minValue(tree, res))
{
}

//SPEC
pub fn GetMax(tree: Tree) -> (res: int)
    requires(BinarySearchTree(tree))
    ensures(maxValue(tree, res))
{
}

//SPEC
pub fn insert(tree: Tree, value: int) -> (res: Tree)
    requires(BinarySearchTree(tree))
    ensures(BinarySearchTree(res))
{
}

//SPEC
pub fn insertRecursion(tree: Tree, value: int) -> (res: Tree)
    requires(BinarySearchTree(tree))
    ensures(res != Tree::Empty ==> BinarySearchTree(res))
    ensures(forall |x: int| minValue(tree, x) && x < value ==> minValue(res, x))
    ensures(forall |x: int| maxValue(tree, x) && x > value ==> maxValue(res, x))
{
}

//SPEC
pub fn delete(tree: Tree, value: int) -> (res: Tree)
    requires(BinarySearchTree(tree))
    ensures(BinarySearchTree(res))
    ensures(res != Tree::Empty ==> BinarySearchTree(res))
{
}

//SPEC
pub fn deleteRecursion(tree: Tree, value: int) -> (res: Tree)
    requires(BinarySearchTree(tree))
    ensures(BinarySearchTree(res))
    ensures(res != Tree::Empty ==> BinarySearchTree(res))
{
}

//ATOM
pub fn Inorder(tree: Tree) {
}

//ATOM
pub fn Postorder(tree: Tree) {
}

//SPEC
pub fn Main() {
}
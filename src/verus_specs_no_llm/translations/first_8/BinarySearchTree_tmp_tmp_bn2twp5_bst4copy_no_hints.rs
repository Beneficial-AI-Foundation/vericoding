// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn BinarySearchTree(tree: Tree) -> bool {
    match tree
  case Empty => true
  case Node(_,_,_) =>
    (tree.left == Empty | tree.left.value < tree.value)
    and (tree.right == Empty .len()| tree.right.value > tree.value)
    and BinarySearchTree(tree.left) and BinarySearchTree(tree.right)
    and minValue(tree.right, tree.value) and maxValue(tree.left, tree.value)
}
spec fn maxValue(tree: Tree, max: int) -> bool {
    match tree
  case Empty => true
  case Node(left,v,right) => (max > v) and maxValue(left, max) and maxValue(right, max)
}
spec fn minValue(tree: Tree, min: int) -> bool {
    match tree
  case Empty => true
  case Node(left,v,right) => (min < v) and minValue(left, min) and minValue(right, min)
}

fn GetMin(tree: Tree) -> (res: int)
    requires BinarySearchTree(tree)
    ensures minValue(tree, res)
{
}

}
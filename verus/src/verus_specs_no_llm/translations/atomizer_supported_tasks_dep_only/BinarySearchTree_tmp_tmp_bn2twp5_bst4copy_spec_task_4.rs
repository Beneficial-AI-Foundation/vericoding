// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn BinarySearchTree(tree: Tree) -> bool {
    match tree
  case Empty => true
  case Node(_,_,_) =>
    (tree.left == Empty | tree.left.value < tree.value)
    && (tree.right == Empty .len()| tree.right.value > tree.value)
    && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
    && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}
spec fn maxValue(tree: Tree, max: int) -> bool {
    match tree
  case Empty => true
  case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}
spec fn minValue(tree: Tree, min: int) -> bool {
    match tree
  case Empty => true
  case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}

fn insertRecursion(tree: Tree, value: int) -> (res: Tree)
    requires
        BinarySearchTree(tree)
    ensures
        res != Empty ==> BinarySearchTree(res),
        forall x :: minValue(tree, x) && x < value ==> minValue(res, x),
        forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
    return 0;
}

}
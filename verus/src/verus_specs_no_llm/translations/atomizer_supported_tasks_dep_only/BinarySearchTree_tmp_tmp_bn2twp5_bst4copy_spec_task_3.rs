// Translated from Dafny
use builtin::*;
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

spec fn spec_insert(tree: Tree, value: int) -> res: Tree
    requires
        BinarySearchTree(tree)
    ensures
        BinarySearchTree(res)
;

proof fn lemma_insert(tree: Tree, value: int) -> (res: Tree)
    requires
        BinarySearchTree(tree)
    ensures
        BinarySearchTree(res)
{
    0
}

}
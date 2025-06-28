// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn minValue(tree: Tree, min: int) -> bool {
    match tree
 case Empty => true
 case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
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

fn insert(tree: Tree, value: int) -> (res: Tree)
 requires BinarySearchTree(tree)
 ensures BinarySearchTree(res)
{
  res := Empty;
  assume BinarySearchTree(res);
  return res;
}


//ATOM

predicate minValue(tree: Tree, min: int)
{
 match tree
 case Empty => true
 case Node(left, v, right) => (min < v) && minValue(left, min) && minValue(right, min)
}


//ATOM

predicate BinarySearchTree(tree: Tree)
{
 match tree
 case Empty => true
 case Node(_, _, _) =>
  (tree.left == Empty || tree.left.value < tree.value)
  && (tree.right == Empty || tree.right.value > tree.value)
  && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
  && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}


//ATOM

predicate maxValue(tree: Tree, max: int)
{
 match tree
 case Empty => true
 case Node(left, v, right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}


//ATOM

method GetMin(tree: Tree) returns (res: int)
{
  res := 0;
  return res;
}


//ATOM

method Inorder(tree: Tree)
    requires
        BinarySearchTree(tree)
    ensures
        BinarySearchTree(res)
{
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
}

}
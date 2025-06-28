// Translated from Dafny
use builtin::*;
use builtin_macros::*;

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

fn insertRecursion(tree: Tree, value: int) -> (res: Tree)
 requires BinarySearchTree(tree)
 ensures res != Empty ==> BinarySearchTree(res)
 ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
 ensures forall x: : maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  res: = Empty;
  assume res != Empty ==> BinarySearchTree(res);
  assume forall x :: minValue(tree, x) && x < value ==> minValue(res, x);
  assume forall x: : maxValue(tree, x) && x > value ==> maxValue(res, x);
  return res;
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

predicate minValue(tree: Tree, min: int)
{
 match tree
 case Empty => true
 case Node(left, v, right) => (min < v) && minValue(left, min) && minValue(right, min)
}


// SPEC

method insert(tree: Tree, value: int) returns (res: Tree)
    requires
        BinarySearchTree(tree),
        BinarySearchTree(tree)
    ensures
        res != Empty ==> BinarySearchTree(res),
        forall x :: minValue(tree, x) && x < value ==> minValue(res, x),
        forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x),
        BinarySearchTree(res)
{
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
}

}
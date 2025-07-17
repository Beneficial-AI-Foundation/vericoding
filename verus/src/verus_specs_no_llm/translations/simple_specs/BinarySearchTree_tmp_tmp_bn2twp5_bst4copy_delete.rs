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
spec fn minValue(tree: Tree, min: int) -> bool {
    match tree
 case Empty => true
 case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}
spec fn maxValue(tree: Tree, max: int) -> bool {
    match tree
 case Empty => true
 case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}

spec fn spec_GetMin(tree: Tree) -> res: int)
{
  res := 0;
  return res;
}


//ATOM

predicate BinarySearchTree(tree: Tree)
{
 match tree
 case Empty => true
 case Node(_,_,_) =>
  (tree.left == Empty || tree.left.value < tree.value)
  && (tree.right == Empty || tree.right.value > tree.value)
  && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
  && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}


//ATOM

predicate minValue(tree: Tree, min: int)
{
 match tree
 case Empty => true
 case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}


//ATOM

predicate maxValue(tree: Tree, max: int)
{
 match tree
 case Empty => true
 case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}


// SPEC

method delete(tree: Tree, value: int) returns (res: Tree
    requires
        BinarySearchTree(tree)
 //
    ensures
        BinarySearchTree(res)
 //,
        res != Empty ==> BinarySearchTree(res)
;

proof fn lemma_GetMin(tree: Tree) -> (res: int)
{
  res := 0;
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

predicate minValue(tree: Tree, min: int)
{
 match tree
 case Empty => true
 case Node(left, v, right) => (min < v) && minValue(left, min) && minValue(right, min)
}


//ATOM

predicate maxValue(tree: Tree, max: int)
{
 match tree
 case Empty => true
 case Node(left, v, right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}


// SPEC

method delete(tree: Tree, value: int) returns (res: Tree)
    requires
        BinarySearchTree(tree)
 //
    ensures
        BinarySearchTree(res)
 //,
        res != Empty ==> BinarySearchTree(res)
{
    (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
}

}
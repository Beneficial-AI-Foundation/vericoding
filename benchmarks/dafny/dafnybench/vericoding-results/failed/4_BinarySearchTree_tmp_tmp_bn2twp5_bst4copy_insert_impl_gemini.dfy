// <vc-preamble>
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

predicate BinarySearchTree(tree: Tree)
  decreases tree
{
  match tree
  case Empty => true
  case Node(_,_,_) =>
    (tree.left == Empty || tree.left.value < tree.value)
    && (tree.right == Empty || tree.right.value > tree.value)
    && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
    && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}

predicate maxValue(tree: Tree, max: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}

predicate minValue(tree: Tree, min: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): defined a functional version of insert to aid verification */
function insert_func(tree: Tree, value: int): (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
  ensures forall x :: maxValue(tree, x) && value < x ==> maxValue(res, x)
  ensures forall x :: minValue(tree, x) && value > x ==> minValue(res, x)
  decreases tree
{
  match tree
  case Empty => Node(Empty, value, Empty)
  case Node(left, v, right) =>
    if value < v then
      Node(insert_func(left, value), v, right)
    else if value > v then
      Node(left, v, insert_func(right, value))
    else
      tree
}
// </vc-helpers>

// <vc-spec>
method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures BinarySearchTree(res)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): use a pure function for insertion logic */
{
  res := insert_func(tree, value);
}
// </vc-code>

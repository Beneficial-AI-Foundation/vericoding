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

// <vc-helpers>
ghost function {:opaque} size(tree: Tree): nat {
  match tree
  case Empty => 0
  case Node(left, _, right) => 1 + size(left) + size(right)
}

method insertRecursionImpl(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases size(tree)
  ensures BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  if tree == Empty {
    res := Node(Empty, value, Empty);
  } else if value < tree.value {
    var newLefpos := insertRecursionImpl(tree.left, value);
    res := Node(newLeft, tree.value, tree.right);
  } else if value == tree.value {
    res := tree;
  } else {
    var newRight := insertRecursionImpl(tree.right, value);
    res := Node(tree.left, tree.value, newRight);
  }
}
// </vc-helpers>

// <vc-spec>
method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures BinarySearchTree(res)
// </vc-spec>
// <vc-code>
{
    res := insertRecursionImpl(tree, value);
}
// </vc-code>


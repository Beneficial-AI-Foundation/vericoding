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
lemma insertRecursionPreservesOrder(tree: Tree, value: int, res: Tree)
  requires BinarySearchTree(tree)
  requires res == insertRecursionImpl(tree, value)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  match tree
  case Empty => 
    assert res == Node(Empty, value, Empty);
  case Node(left, v, right) =>
    if value < v {
      insertRecursionPreservesOrder(left, value, insertRecursionImpl(left, value));
    } else if value > v {
      insertRecursionPreservesOrder(right, value, insertRecursionImpl(right, value));
    }
}

function insertRecursionImpl(tree: Tree, value: int): Tree
  requires BinarySearchTree(tree)
  decreases tree
{
  match tree
  case Empty => Node(Empty, value, Empty)
  case Node(left, v, right) =>
    if value < v then
      Node(insertRecursionImpl(left, value), v, right)
    else if value > v then
      Node(left, v, insertRecursionImpl(right, value))
    else
      tree
}

lemma insertRecursionCorrect(tree: Tree, value: int)
  requires BinarySearchTree(tree)
  ensures var res := insertRecursionImpl(tree, value); 
          res != Empty && BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(insertRecursionImpl(tree, value), x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(insertRecursionImpl(tree, value), x)
{
  var res := insertRecursionImpl(tree, value);
  match tree
  case Empty => 
    assert res == Node(Empty, value, Empty);
    assert BinarySearchTree(res);
  case Node(left, v, right) =>
    if value < v {
      insertRecursionCorrect(left, value);
    } else if value > v {
      insertRecursionCorrect(right, value);
    }
}

method insertRecursionCorrectImpl(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures res != Empty && BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
  decreases tree
{
  res := insertRecursionImpl(tree, value);
  insertRecursionCorrect(tree, value);
  insertRecursionPreservesOrder(tree, value, res);
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
  res := insertRecursionCorrectImpl(tree, value);
}
// </vc-code>


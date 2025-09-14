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

// <vc-helpers>
function insertFunction(tree: Tree, value: int): Tree
  requires BinarySearchTree(tree)
  decreases tree
{
  match tree
  case Empty => Node(Empty, value, Empty)
  case Node(left, v, right) =>
    if value < v then
      Node(insertFunction(left, value), v, right)
    else if value > v then
      Node(left, v, insertFunction(right, value))
    else
      tree
}

lemma insertPreservesMinValue(tree: Tree, value: int, x: int)
  requires BinarySearchTree(tree)
  requires minValue(tree, x) && x < value
  decreases tree
  ensures minValue(insertFunction(tree, value), x)
{
  match tree
  case Empty => {}
  case Node(left, v, right) =>
    if value < v {
      insertPreservesMinValue(left, value, x);
    } else if value > v {
      insertPreservesMinValue(right, value, x);
    }
}

lemma insertPreservesMaxValue(tree: Tree, value: int, x: int)
  requires BinarySearchTree(tree)
  requires maxValue(tree, x) && x > value
  decreases tree
  ensures maxValue(insertFunction(tree, value), x)
{
  match tree
  case Empty => {}
  case Node(left, v, right) =>
    if value < v {
      insertPreservesMaxValue(left, value, x);
    } else if value > v {
      insertPreservesMaxValue(right, value, x);
    }
}

lemma insertPreservesMinValueForRight(tree: Tree, value: int, nodeValue: int)
  requires BinarySearchTree(tree)
  requires value < nodeValue
  decreases tree
  ensures minValue(insertFunction(tree, value), nodeValue)
{
  match tree
  case Empty => {}
  case Node(left, v, right) =>
    if minValue(tree, nodeValue) {
      insertPreservesMinValue(tree, value, nodeValue);
    }
}

lemma insertPreservesMaxValueForLeft(tree: Tree, value: int, nodeValue: int)
  requires BinarySearchTree(tree)
  requires value > nodeValue
  decreases tree
  ensures maxValue(insertFunction(tree, value), nodeValue)
{
  match tree
  case Empty => {}
  case Node(left, v, right) =>
    if maxValue(tree, nodeValue) {
      insertPreservesMaxValue(tree, value, nodeValue);
    }
}

lemma insertPreservesBST(tree: Tree, value: int)
  requires BinarySearchTree(tree)
  decreases tree
  ensures BinarySearchTree(insertFunction(tree, value))
{
  match tree
  case Empty => {}
  case Node(left, v, right) =>
    if value < v {
      insertPreservesBST(left, value);
      if maxValue(left, v) {
        insertPreservesMaxValueForLeft(left, value, v);
      }
    } else if value > v {
      insertPreservesBST(right, value);
      if minValue(right, v) {
        insertPreservesMinValueForRight(right, value, v);
      }
    }
}
// </vc-helpers>

// <vc-spec>
method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
// </vc-spec>
// <vc-code>
{
  res := insertFunction(tree, value);
  insertPreservesBST(tree, value);
  
  forall x | minValue(tree, x) && x < value
    ensures minValue(res, x)
  {
    insertPreservesMinValue(tree, value, x);
  }
  
  forall x | maxValue(tree, x) && x > value
    ensures maxValue(res, x)
  {
    insertPreservesMaxValue(tree, value, x);
  }
}
// </vc-code>


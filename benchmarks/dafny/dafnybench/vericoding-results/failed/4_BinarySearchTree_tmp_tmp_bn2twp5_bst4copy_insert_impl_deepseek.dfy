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
predicate maxValue2(tree: Tree, max: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (v < max) && maxValue2(left, max) && maxValue2(right, max)
}

predicate minValue2(tree: Tree, min: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (v > min) && minValue2(left, min) && minValue2(right, min)
}

lemma {:induction false} InsertPreservesMinValue(tree: Tree, value: int, x: int)
  requires BinarySearchTree(tree)
  requires minValue2(tree, x)
  requires x < value
  ensures minValue2(insertRecursion(tree, value), x)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    if value < v {
      InsertPreservesMinValue(left, value, x);
    } else if value > v {
      InsertPreservesMinValue(right, value, x);
    }
}

lemma {:induction false} InsertPreservesMaxValue(tree: Tree, value: int, x: int)
  requires BinarySearchTree(tree)
  requires maxValue2(tree, x)
  requires x > value
  ensures maxValue2(insertRecursion(tree, value), x)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    if value < v {
      InsertPreservesMaxValue(left, value, x);
    } else if value > v {
      InsertPreservesMaxValue(right, value, x);
    }
}

lemma {:induction false} InsertPreservesBST(tree: Tree, value: int)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(insertRecursion(tree, value))
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    if value < v {
      InsertPreservesBST(left, value);
    } else if value > v {
      InsertPreservesBST(right, value);
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
  match tree {
    case Empty => 
      res := Node(Empty, value, Empty);
    case Node(left, v, right) =>
      if value < v {
        var newLeft := insertRecursion(left, value);
        res := Node(newLeft, v, right);
      } else if value > v {
        var newRight := insertRecursion(right, value);
        res := Node(left, v, newRight);
      } else {
        res := tree;
      }
  }
}
// </vc-code>


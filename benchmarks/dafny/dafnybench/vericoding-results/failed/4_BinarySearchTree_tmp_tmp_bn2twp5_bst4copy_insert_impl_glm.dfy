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
lemma MinValueInsert(tree: Tree, value: int, min: int)
  requires BinarySearchTree(tree)
  requires minValue(tree, min)
  requires min < value
  ensures minValue(insert(tree, value), min)
{
  match tree
  case Empty =>
    // minValue(Node(Empty, value, Empty), min) holds because min < value (given) and minValue(Empty, min) holds (by definition)
  case Node(left, v, right) =>
    if value < v {
      MinValueInsert(left, value, min);
      // New tree: Node(insert(left, value), v, right)
      // min < v (from minValue(tree, min)) and minValue(insert(left, value), min) (by lemma) and minValue(right, min) (unchanged)
    } else if v < value {
      MinValueInsert(right, value, min);
      // New tree: Node(left, v, insert(right, value))
      // min < v (from minValue(tree, min)) and minValue(left, min) (unchanged) and minValue(insert(right, value), min) (by lemma)
    } else {
      // v == value: tree remains unchanged after insertion
      // minValue(tree, min) holds by precondition
    }
}

lemma MaxValueInsert(tree: Tree, value: int, max: int)
  requires BinarySearchTree(tree)
  requires maxValue(tree, max)
  requires value < max
  ensures maxValue(insert(tree, value), max)
{
  match tree
  case Empty =>
    // maxValue(Node(Empty, value, Empty), max) holds because value < max (given) and maxValue(Empty, max) holds (by definition)
  case Node(left, v, right) =>
    if value < v {
      MaxValueInsert(left, value, max);
      // New tree: Node(insert(left, value), v, right)
      // max > v (from maxValue(tree, max)) and maxValue(insert(left, value), max) (by lemma) and maxValue(right, max) (unchanged)
    } else if v < value {
      MaxValueInsert(right, value, max);
      // New tree: Node(left, v, insert(right, value))
      // max > v (from maxValue(tree, max)) and maxValue(left, max) (unchanged) and maxValue(insert(right, value), max) (by lemma)
    } else {
      // v == value: tree remains unchanged after insertion
      // maxValue(tree, max) holds by precondition
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
  if tree == Empty {
    return Node(Empty, value, Empty);
  } else {
    var left := tree.left;
    var right := tree.right;
    var v := tree.value;

    if value < v {
      var oldLeft := left;
      left := insert(left, value);
      MaxValueInsert(oldLeft, value, v);
    } else if v < value {
      var oldRight := right;
      right := insert(right, value);
      MinValueInsert(oldRight, value, v);
    }
    return Node(left, v, right);
  }
}
// </vc-code>


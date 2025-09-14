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
lemma updateMinValue(tree: Tree, min: int, value: int)
  requires BinarySearchTree(tree)
  requires min < value
  ensures minValue(tree, min)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    updateMinValue(left, min, value);
    updateMinValue(right, min, value);
}

lemma updateMaxValue(tree: Tree, max: int, value: int)
  requires BinarySearchTree(tree)
  requires max > value
  ensures maxValue(tree, max)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    updateMaxValue(left, max, value);
    updateMaxValue(right, max, value);
}

lemma minValuePreserved(tree: Tree, min: int, value: int)
  requires BinarySearchTree(tree)
  requires minValue(tree, min)
  requires min < value
  ensures minValue(tree, min)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    minValuePreserved(left, min, value);
    minValuePreserved(right, min, value);
}

lemma maxValuePreserved(tree: Tree, max: int, value: int)
  requires BinarySearchTree(tree)
  requires maxValue(tree, max)
  requires max > value
  ensures maxValue(tree, max)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    maxValuePreserved(left, max, value);
    maxValuePreserved(right, max, value);
}

lemma minValueTransitive(tree: Tree, min: int, mid: int)
  requires BinarySearchTree(tree)
  requires minValue(tree, min)
  requires min < mid
  ensures minValue(tree, mid)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    minValueTransitive(left, min, mid);
    minValueTransitive(right, min, mid);
}

lemma maxValueTransitive(tree: Tree, max: int, mid: int)
  requires BinarySearchTree(tree)
  requires maxValue(tree, max)
  requires max > mid
  ensures maxValue(tree, mid)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    maxValueTransitive(left, max, mid);
    maxValueTransitive(right, max, mid);
}

lemma minValueNodeLeft(tree: Tree, value: int)
  requires BinarySearchTree(tree)
  requires tree != Empty && tree.value == value
  ensures minValue(tree.left, value)
{
  // This holds by definition of BinarySearchTree
}

lemma maxValueNodeRight(tree: Tree, value: int)
  requires BinarySearchTree(tree)
  requires tree != Empty && tree.value == value
  ensures maxValue(tree.right, value)
{
  // This holds by definition of BinarySearchTree
}

lemma minValueAll(tree: Tree, min: int)
  requires BinarySearchTree(tree)
  requires forall x :: x in tree ==> x > min
  ensures minValue(tree, min)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    minValueAll(left, min);
    minValueAll(right, min);
}

lemma maxValueAll(tree: Tree, max: int)
  requires BinarySearchTree(tree)
  requires forall x :: x in tree ==> x < max
  ensures maxValue(tree, max)
{
  match tree
  case Empty =>
  case Node(left, v, right) =>
    maxValueAll(left, max);
    maxValueAll(right, max);
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
  match tree
  case Empty =>
    res := Node(Empty, value, Empty);
    // For the new node, all existing min/max properties are preserved
    // and the new value satisfies min/max conditions
  case Node(left, v, right) =>
    if value < v {
      var newLeft := insertRecursion(left, value);
      res := Node(newLeft, v, right);
      
      // Update min/max properties for the entire tree
      if value < v {
        updateMinValue(right, value, v);
        updateMaxValue(newLeft, v, value);
      }
    } else if value > v {
      var newRight := insertRecursion(right, value);
      res := Node(left, v, newRight);
      
      // Update min/max properties for the entire tree
      if value > v {
        updateMinValue(newRight, v, value);
        updateMaxValue(left, v, value);
      }
    } else {
      res := tree;
    }
}
// </vc-code>


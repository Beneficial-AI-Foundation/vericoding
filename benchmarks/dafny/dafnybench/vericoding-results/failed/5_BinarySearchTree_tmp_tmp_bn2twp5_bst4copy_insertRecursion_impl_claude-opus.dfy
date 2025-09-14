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
lemma maxValueTransitive(tree: Tree, x: int, y: int)
  requires maxValue(tree, x)
  requires x <= y
  ensures maxValue(tree, y)
  decreases tree
{
  match tree
  case Empty => {}
  case Node(left, v, right) => {
    maxValueTransitive(left, x, y);
    maxValueTransitive(right, x, y);
  }
}

lemma minValueTransitive(tree: Tree, x: int, y: int)
  requires minValue(tree, x)
  requires x >= y
  ensures minValue(tree, y)
  decreases tree
{
  match tree
  case Empty => {}
  case Node(left, v, right) => {
    minValueTransitive(left, x, y);
    minValueTransitive(right, x, y);
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
  match tree
  case Empty => {
    res := Node(Empty, value, Empty);
  }
  case Node(left, v, right) => {
    if value < v {
      var newLeft := insertRecursion(left, value);
      res := Node(newLeft, v, right);
      
      if newLeft != Empty {
        assert BinarySearchTree(tree);
        assert minValue(right, v);
        
        assert BinarySearchTree(left);
        assert BinarySearchTree(newLeft);
        assert newLeft.value < v;
        
        assert forall x :: minValue(left, x) && x < value ==> minValue(newLeft, x);
        
        // For minValue(newLeft, v): Since v > value and we inserted value into left,
        // and all values in newLeft are < v (BST property), minValue(newLeft, v) holds
        assert maxValue(newLeft, v);
        minValueTransitive(right, v, v);
        assert minValue(right, v);
      }
    } else if value > v {
      var newRight := insertRecursion(right, value);
      res := Node(left, v, newRight);
      
      if newRight != Empty {
        assert BinarySearchTree(tree);
        assert maxValue(left, v);
        
        assert BinarySearchTree(right);
        assert BinarySearchTree(newRight);
        assert newRight.value > v;
        
        assert forall x :: maxValue(right, x) && x > value ==> maxValue(newRight, x);
        
        // For maxValue(newRight, v): Since v < value and we inserted value into right,
        // and all values in newRight are > v (BST property), maxValue(newRight, v) holds
        assert minValue(newRight, v);
        maxValueTransitive(left, v, v);
        assert maxValue(left, v);
      }
    } else {
      res := tree;
    }
  }
}
// </vc-code>


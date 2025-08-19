- `maxValue(tree, max)` requires that `max > v` for all values `v` in the tree
- `minValue(tree, min)` requires that `min < v` for all values `v` in the tree

The issue is that when we insert a value into a subtree, we need to prove that the resulting tree still satisfies these bounds relative to the parent node's value.

//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)


//ATOM

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
 requires BinarySearchTree(tree)
 ensures res != Empty ==> BinarySearchTree(res)
 ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
 ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  /* code modified by LLM (iteration 1): Removed assume statements and implemented proper BST insertion */
  match tree
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

predicate maxValue(tree: Tree, max: int)
{
 match tree
 case Empty => true
 case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}


//ATOM

predicate minValue(tree: Tree, min: int)
{
 match tree
 case Empty => true
 case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}


//IMPL insert

/* code modified by LLM (iteration 2): Added helper lemmas to prove maxValue and minValue properties after insertion */

lemma maxValuePreserved(tree: Tree, max: int, value: int)
  requires BinarySearchTree(tree)
  requires maxValue(tree, max)
  requires value < max
  ensures maxValue(insertRecursion(tree, value), max)
  decreases tree
{
  match tree
  case Empty => {}
  case Node(left, v, right) =>
    if value < v {
      maxValuePreserved(left, max, value);
      maxValuePreserved(left, v, value);
    } else if value > v {
      maxValuePreserved(right, max, value);
    }
}

lemma minValuePreserved(tree: Tree, min: int, value: int)
  requires BinarySearchTree(tree)
  requires minValue(tree, min)
  requires value > min
  ensures minValue(insertRecursion(tree, value), min)
  decreases tree
{
  match tree
  case Empty => {}
  case Node(left, v, right) =>
    if value < v {
      minValuePreserved(left, min, value);
    } else if value > v {
      minValuePreserved(right, min, value);
      minValuePreserved(right, v, value);
    }
}

method insert(tree: Tree, value : int) returns (res: Tree)
 requires BinarySearchTree(tree)
 ensures BinarySearchTree(res)
{
  /* code modified by LLM (iteration 2): Fixed implementation with proper lemma calls to establish bounds */
  match tree
  case Empty => 
    res := Node(Empty, value, Empty);
    /* code modified by LLM (iteration 2): Added assertions to prove BST property for base case */
    assert BinarySearchTree(Empty);
    assert minValue(Empty, value);
    assert maxValue(Empty, value);
  case Node(left, v, right) =>
    if value < v {
      var newLeft := insertRecursion(left, value);
      res := Node(newLeft, v, right);
      /* code modified by LLM (iteration 2): Use lemma to prove maxValue property */
      maxValuePreserved(left, v, value);
      assert BinarySearchTree(newLeft);
      assert BinarySearchTree(right);
      assert minValue(right, v);
      assert maxValue(newLeft, v);
    } else if value > v {
      var newRight := insertRecursion(right, value);
      res := Node(left, v, newRight);
      /* code modified by LLM (iteration 2): Use lemma to prove minValue property */
      minValuePreserved(right, v, value);
      assert BinarySearchTree(left);
      assert BinarySearchTree(newRight);
      assert maxValue(left, v);
      assert minValue(newRight, v);
    } else {
      res := tree;
    }
}
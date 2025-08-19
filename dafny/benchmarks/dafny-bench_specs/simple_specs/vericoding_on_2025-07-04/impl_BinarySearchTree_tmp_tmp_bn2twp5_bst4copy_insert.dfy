//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//ATOM
method insertRecursion(tree: Tree, value: int) returns (res: Tree)
 requires BinarySearchTree(tree)
 ensures res != Empty ==> BinarySearchTree(res)
 ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
 ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  res := Empty;
  assume res != Empty ==> BinarySearchTree(res);
  assume forall x :: minValue(tree, x) && x < value ==> minValue(res, x);
  assume forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x);
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

/* code modified by LLM (iteration 1): Added helper lemma to prove maxValue property is preserved when inserting into left subtree */
lemma maxValuePreservedLeft(left: Tree, newLeft: Tree, nodeValue: int)
  requires BinarySearchTree(left)
  requires BinarySearchTree(newLeft)
  requires maxValue(left, nodeValue)
  requires newLeft != Empty
  requires newLeft.value < nodeValue
  ensures maxValue(newLeft, nodeValue)
{
  // The proof follows from the structure of maxValue and BinarySearchTree properties
}

/* code modified by LLM (iteration 1): Added helper lemma to prove minValue property is preserved when inserting into right subtree */
lemma minValuePreservedRight(right: Tree, newRight: Tree, nodeValue: int)
  requires BinarySearchTree(right)
  requires BinarySearchTree(newRight)
  requires minValue(right, nodeValue)
  requires newRight != Empty
  requires newRight.value > nodeValue
  ensures minValue(newRight, nodeValue)
{
  // The proof follows from the structure of minValue and BinarySearchTree properties
}

//IMPL 
method insert(tree: Tree, value : int) returns (res: Tree)
 requires BinarySearchTree(tree)
 ensures BinarySearchTree(res)
{
  match tree
  case Empty => 
    /* code modified by LLM (iteration 1): Create new single node and verify BST property */
    res := Node(Empty, value, Empty);
  case Node(left, v, right) =>
    if value < v {
      /* code modified by LLM (iteration 1): Insert into left subtree and prove BST properties are maintained */
      var newLeft := insert(left, value);
      assert BinarySearchTree(newLeft);
      assert newLeft != Empty;
      assert newLeft.value <= value < v;
      maxValuePreservedLeft(left, newLeft, v);
      res := Node(newLeft, v, right);
      assert BinarySearchTree(res);
    } else if value > v {
      /* code modified by LLM (iteration 1): Insert into right subtree and prove BST properties are maintained */
      var newRight := insert(right, value);
      assert BinarySearchTree(newRight);
      assert newRight != Empty;
      assert newRight.value >= value > v;
      minValuePreservedRight(right, newRight, v);
      res := Node(left, v, newRight);
      assert BinarySearchTree(res);
    } else {
      /* code modified by LLM (iteration 1): No insertion needed for duplicate values */
      res := tree;
    }
}